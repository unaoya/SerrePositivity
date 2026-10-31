#!/usr/bin/env python3
"""Collect disjoint hash-only Lean snapshots serially in a fresh directory."""
import argparse
import json
from pathlib import Path
import subprocess
import time

from lean_source import transient_names

ROOT = Path(__file__).resolve().parents[2]
HEAVY = tuple("SerrePositivity." + name for name in
              ("KST.SConstruction", "InfinityCategories.Derived", "EInfinity"))


def groups(modules):
    pending = []
    limit = None
    for module in modules:
        heavy = any(module == prefix or module.startswith(prefix + ".") for prefix in HEAVY)
        next_limit = 16 if heavy else 64
        if pending and (len(pending) == limit or next_limit != limit):
            yield pending
            pending = []
        limit = next_limit
        pending.append(module)
    if pending:
        yield pending


def memory_failure(code, log):
    return code in (-9, 137) or (code != 0 and any(
        message in log.lower() for message in
        ("out of memory", "maximum memory", "memory limit", "excessive memory", "bad_alloc")))


def write_inventory(path, terms, completed, total):
    rows = sorted(terms, key=lambda row: (-int(row["expanded_bytes"]), row["module"], row["name"], row["field"]))
    lines = ["# 木に展開すると1 GBを超える項", "",
             f"§10.19 の before snapshot。採取済み {completed:,} / {total:,} モジュール、該当 {len(rows):,} 項。",
             "展開サイズは旧形式の compact JSON の UTF-8 バイト数を DAG 上で数えた値。閾値は 1,000,000,000 バイト超。異なる部分式数は Expr の構造的同値で数える。",
             "段 G・K-S• 再開時の調査候補。監査の RSS との関係は IF-W0-4 の実測と照合する。", "",
             "| モジュール | 宣言 | 対象 | 異なる部分式数 | 展開サイズ（bytes） |",
             "|---|---|---|---:|---:|"]
    for row in rows:
        name = row["name"].replace("|", "&#124;")
        lines.append(f'| `{row["module"]}` | `{name}` | {row["field"]} | '
                     f'{int(row["distinct_subexpressions"]):,} | {int(row["expanded_bytes"]):,} |')
    tmp = path.with_suffix(".md.tmp")
    tmp.write_text("\n".join(lines) + "\n")
    tmp.replace(path)


def collect(modules, name_map, directory, inventory=None):
    if not modules or len(set(modules)) != len(modules):
        raise ValueError("expected a nonempty list of distinct modules")
    rules = json.loads(name_map.read_text())
    directory.mkdir(parents=True, exist_ok=False)
    terms = []
    started = time.monotonic()
    state = {"status": "RUNNING", "total": len(modules), "completed": 0, "attempts": []}
    def save():
        state["seconds"] = round(time.monotonic() - started, 3)
        pending = directory / "manifest.tmp"
        pending.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n")
        pending.replace(directory / "manifest.json")

    def take(subset, label):
        out = directory / (label + ".json")
        log = directory / (label + ".log")
        command = ["lake", "env", "lean", "-M", "40000", "--run", "scripts/refactor/decl_snapshot.lean",
                   "--modules", ",".join(subset), "--name-map", str(name_map), "--output", str(out)]
        attempt = {"label": label, "modules": subset, "command": command}
        state["attempts"].append(attempt)
        save()
        begin = time.monotonic()
        with log.open("w") as stream:
            code = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT).returncode
        attempt.update(exit_code=code, seconds=round(time.monotonic() - begin, 3))
        save()
        if memory_failure(code, log.read_text()) and len(subset) > 1:
            half = len(subset) // 2
            take(subset[:half], label + "-a")
            take(subset[half:], label + "-b")
            return
        if code:
            raise RuntimeError(f"{label} exited {code}, see {log}")
        snap = json.loads(out.read_text())
        if (snap["schema_version"] != 2 or snap["name_map"] != rules or snap["modules"] != subset
                or snap["hash_algorithm"] != "normalized Expr DAG mixHash v1"
                or snap["count"] != len(snap["declarations"])
                or any("type" in row or "body" in row or "type_hash" not in row or "body_hash" not in row
                       for row in snap["declarations"])):
            raise ValueError(f"{label}: unexpected snapshot format or coverage")
        sources = {s["module"]: s["source"] for s in snap["sources"]}
        if set(sources) != set(subset) or any(
                text != (ROOT / (name.replace(".", "/") + ".lean")).read_text() for name, text in sources.items()):
            raise ValueError(f"{label}: source coverage or contents changed")
        # Attribution also needs the source parser, shared with splitting and comparison.
        snap["transient"] = transient_names(snap)
        temporary = out.with_suffix(".tmp")
        temporary.write_text(json.dumps(snap, ensure_ascii=False) + "\n")
        temporary.replace(out)
        attempt["file"] = out.name
        state["completed"] += len(subset)
        terms.extend(snap["huge_terms"])
        state["huge_term_count"] = len(terms)
        if inventory:
            write_inventory(inventory, terms, state["completed"], len(modules))
        save()

    try:
        for index, subset in enumerate(groups(modules)):
            take(subset, f"shard-{index:03}")
        state["status"] = "PASS"
    except BaseException as exc:
        state.update(status="STOP", error=str(exc))
        raise
    finally:
        save()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modules-file", required=True, type=Path, help="JSON array of module names")
    parser.add_argument("--name-map", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--huge-terms", type=Path, help="Markdown inventory of terms over 1 GB")
    args = parser.parse_args()
    collect(json.loads(args.modules_file.read_text()), args.name_map.resolve(), args.output_dir.resolve(), args.huge_terms)
