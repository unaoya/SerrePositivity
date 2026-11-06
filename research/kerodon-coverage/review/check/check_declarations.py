#!/usr/bin/env python3
"""Kerodon 対応表・段1。数学的な対応の正否は判定しない（Python 標準ライブラリのみ）。"""
from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import json
import re
import subprocess
import sys
import time
import shlex
from datetime import datetime, timezone
from pathlib import Path

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IDENT = r"[^\W\d][\w']*"
NAME = re.compile(rf"{IDENT}(?:\.{IDENT})*\Z", re.UNICODE)
REFERENCE = re.compile(r"(.+?) @ ((?:\.lake/packages/mathlib/)?(?:Mathlib|SerrePositivity)/[^\s:]+\.lean)(?::([1-9]\d*))?\Z")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def write_csv(path, rows, fields):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fields, extrasaction="ignore", lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def reference(raw):
    result = dict(id=hashlib.sha256(raw.encode()).hexdigest()[:20], raw=raw,
                  declaration="", source="", source_line="", module="",
                  preparation="unresolved_reference")
    match = REFERENCE.fullmatch(raw)
    if not match:
        return result
    name, source, line = match.groups()
    source = source.removeprefix(".lake/packages/mathlib/")
    parts = Path(source).with_suffix("").parts
    if not all(NAME.fullmatch(p) and "." not in p for p in parts):
        return result
    result.update(source=source, source_line=line or "", module=".".join(parts))
    # 説明・匿名 instance・略記を推測で定数名に変えない。
    if NAME.fullmatch(name):
        result.update(declaration=name, preparation="ready")
    return result


def provenance(root):
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=root, text=True).strip()
    return {
        "commit": git("rev-parse", "HEAD"),
        "lean_source_changes": git("status", "--porcelain", "--untracked-files=no", "--", "*.lean"),
        "items_sha256": digest(root / "research/kerodon-coverage/items.csv"),
        "targets_sha256": digest(root / "research/kerodon-coverage/review-targets.csv"),
        "manifest_sha256": digest(root / "lake-manifest.json"),
        "toolchain": (root / "lean-toolchain").read_text().strip(),
        "script_sha256": digest(Path(__file__)),
    }


def prepare(root, directory, chapters):
    if directory.exists():
        raise ValueError(f"出力先は既に存在します（上書きしません）: {directory}")
    with (root / "research/kerodon-coverage/items.csv").open(newline="") as f:
        all_items = list(csv.DictReader(f))
    if len({r["number"] for r in all_items}) != len(all_items):
        raise ValueError("items.csv に番号の重複があります")
    with (root / "research/kerodon-coverage/review-targets.csv").open(newline="") as f:
        priority = {r["number"]: r["reason"] for r in csv.DictReader(f)}
    refs, occurrences, items = {}, [], []
    for row in all_items:
        chapter = int(row["number"].split(".")[0])
        if chapters and chapter not in chapters:
            continue
        ids = []
        # status=none に宣言欄があっても検査対象。空の欄だけを除く。
        for index, raw in enumerate(row["declarations"].split(" | ")):
            if not raw.strip():
                continue
            ref = reference(raw.strip())
            if ref["id"] in refs and refs[ref["id"]]["raw"] != ref["raw"]:
                raise ValueError("reference id collision")
            refs[ref["id"]] = ref
            ids.append(ref["id"])
            occurrences.append(dict(number=row["number"], occurrence=index + 1,
                                    reference_id=ref["id"], reason=priority.get(row["number"], ""),
                                    raw=raw))
        items.append(dict(number=row["number"], status=row["status"], references=ids,
                          priority=priority.get(row["number"], "")))
    if not items:
        raise ValueError("対象項目がありません")
    urgent = {ref for item in items if item["priority"] for ref in item["references"]}
    groups = collections.defaultdict(list)
    for ref in refs.values():
        if ref["preparation"] == "ready":
            groups[ref["module"]].append(ref["id"])
    modules = sorted(groups, key=lambda m: (not any(i in urgent for i in groups[m]), m))
    plan = dict(schema=1, provenance=provenance(root), chapters=sorted(chapters),
                items=items, references=list(refs.values()),
                jobs=[dict(module=m, references=groups[m]) for m in modules])
    dump(directory / "plan.json", plan)
    write_csv(directory / "references.csv", occurrences,
              ["number", "occurrence", "reference_id", "reason", "raw"])
    unresolved = [r for r in refs.values() if r["preparation"] != "ready"]
    write_csv(directory / "unresolved.csv", unresolved,
              ["id", "raw", "source", "source_line", "module", "preparation"])
    summary = dict(items=len(items), items_with_references=sum(bool(i["references"]) for i in items),
                   occurrences=len(occurrences), unique_references=len(refs),
                   ready_references=len(refs) - len(unresolved),
                   unresolved_references=len(unresolved), modules=len(modules),
                   status=dict(collections.Counter(i["status"] for i in items)))
    dump(directory / "inventory.json", summary)
    print(json.dumps(summary, ensure_ascii=False))


def lean_input(module, refs):
    lines = [f"import {module}", "", "set_option pp.universes true", "set_option pp.explicit true", ""]
    commands = {}
    for ref in refs:
        lines.append(f"-- reference {ref['id']}")
        check_line = len(lines) + 1
        lines.append(f"#check @{ref['declaration']}")
        axioms_line = len(lines) + 1
        lines.append(f"#print axioms {ref['declaration']}")
        commands[ref["id"]] = dict(check_line=check_line, axioms_line=axioms_line)
        lines.append("")
    return "\n".join(lines).rstrip() + "\n", commands


def axiom_names(message):
    if re.fullmatch(r"'.+' does not depend on any axioms", message.strip(), re.S):
        return []
    match = re.fullmatch(r"'.+' depends on axioms:\s*\[(.*?)\]", message.strip(), re.S)
    if not match:
        return None
    # pp.universes=true は Classical.choice.{u} などを出す。
    # 宇宙引数内にもカンマがありうるので、分割前に注記を除く。
    plain = re.sub(r"\.\{[^{}]*\}", "", match[1])
    names = [s.strip() for s in plain.split(",") if s.strip()]
    return names if all(NAME.fullmatch(s) for s in names) else None


def parse_output(stdout, stderr, returncode, commands):
    """Lean --json のコマンド行位置で帰属。位置不明の失敗は成功扱いしない。"""
    messages, invalid = [], []
    for line in stdout.splitlines():
        if not line.strip():
            continue
        try:
            message = json.loads(line)
            if not isinstance(message, dict) or not isinstance(message.get("pos", {}).get("line"), int):
                raise ValueError("missing position")
            if not isinstance(message.get("data"), str) or not isinstance(message.get("severity"), str):
                raise ValueError("missing message data")
            messages.append(message)
        except (ValueError, TypeError, AttributeError):
            invalid.append(line)
    command_lines = {line for c in commands.values() for line in c.values()}
    global_errors = [m["data"] for m in messages
                     if m["severity"] == "error" and m["pos"]["line"] not in command_lines]
    errors_seen = any(m["severity"] == "error" for m in messages)
    results = {}
    for ref_id, c in commands.items():
        checks = [m for m in messages if m["pos"]["line"] == c["check_line"]]
        axioms = [m for m in messages if m["pos"]["line"] == c["axioms_line"]]
        errors = [m["data"] for m in checks + axioms if m["severity"] == "error"]
        types = [m["data"] for m in checks if m["severity"] == "information"]
        axtexts = [m["data"] for m in axioms if m["severity"] == "information"]
        names = axiom_names(axtexts[0]) if len(axtexts) == 1 else None
        if invalid or global_errors or stderr.strip() or returncode not in (0, 1) or (returncode and not errors_seen):
            state = "output_invalid"
        elif errors:
            # 型推論・構文・資源エラーを「不存在」に変換しない。
            state = "not_found" if all(re.search(r"Unknown (?:constant|identifier)", e, re.I) for e in errors) else "check_failed"
        elif not types:
            state = "check_failed"
        elif names is None:
            state = "axioms_unparsed"
        else:
            state = "found"
        results[ref_id] = dict(state=state, type="\n".join(types),
                               axioms=names, extra_axioms=sorted(set(names or []) - STANDARD_AXIOMS),
                               axioms_output="\n".join(axtexts),
                               diagnostics="\n".join(errors + global_errors + invalid + ([stderr] if stderr.strip() else [])))
    return results


def call(root, command, stdout_path, stderr_path):
    """zshenv を読み、コマンド引数は shell 文字列へ展開しない。"""
    with stdout_path.open("w") as out, stderr_path.open("w") as err:
        process = subprocess.run(["/bin/zsh", "-c", 'source ~/.zshenv; exec "$@"',
                                  "kerodon-check", *command], cwd=root, stdout=out, stderr=err)
    return process.returncode


def blocking_build(command, cwd):
    if "SerrePositivity" not in cwd:
        return False
    words = shlex.split(command)
    if any(Path(w).name == "verify.sh" for w in words):
        return True
    for i, word in enumerate(words[:-1]):
        if Path(word).name == "lake" and words[i + 1] == "build":
            targets = [w for w in words[i + 2:] if not w.startswith("-")]
            return not targets or any(w in {"SerrePositivity", "SerrePositivity:leanArts"} for w in targets)
    return False


def inspect_builds(root, jobdir):
    result = subprocess.run(["ps", "-axo", "pid=,command="], cwd=root, capture_output=True, text=True)
    records, blocked = [], False
    for line in result.stdout.splitlines():
        if not re.search(r"(?:^|[/\s])lake\s+build(?:\s|$)|verify\.sh", line):
            continue
        parts = line.strip().split(None, 1)
        if len(parts) != 2:
            continue
        pid, command = parts
        location = subprocess.run(["/usr/sbin/lsof", "-a", "-p", pid, "-d", "cwd", "-Fn"], capture_output=True, text=True)
        cwd = next((x[1:] for x in location.stdout.splitlines() if x.startswith("n")), "")
        records.append(dict(pid=pid, command=command, cwd=cwd))
        blocked = blocked or blocking_build(command, cwd)
    dump(jobdir / "build-processes.json", records)
    (jobdir / "ps.stderr.txt").write_text(result.stderr)
    if result.returncode:
        return "preflight_failed"
    return "build_busy" if blocked else "ready"


def run(root, directory, plan, only_modules, limit, resume):
    if provenance(root) != plan["provenance"]:
        raise ValueError("計画作成時から HEAD/入力/スクリプト/Lean ソースが変化。別 run-dir で prepare してください")
    refs = {r["id"]: r for r in plan["references"]}
    mathlib = root / ".lake/packages/mathlib"
    if mathlib.is_dir():
        expected = next(p["rev"] for p in json.loads((root / "lake-manifest.json").read_text())["packages"] if p["name"] == "mathlib")
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip()
        dirty = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no", "--", "*.lean"], cwd=mathlib, text=True).strip()
        if expected != actual or dirty:
            raise ValueError("Mathlib の revision が manifest と異なるか、Lean ソースに未コミット変更があります")
    jobs = [j for j in plan["jobs"] if not only_modules or j["module"] in only_modules]
    unknown = only_modules - {j["module"] for j in plan["jobs"]}
    if unknown:
        raise ValueError(f"計画にないモジュール: {sorted(unknown)}")
    count = 0
    for job in jobs:
        jobdir = directory / "modules" / job["module"]
        metadata_path = jobdir / "execution.json"
        if metadata_path.exists():
            previous = json.loads(metadata_path.read_text())
            if resume and previous["state"] == "checked":
                continue
            raise ValueError(f"既存の試行を上書きしません: {jobdir}（別 run-dir を使用）")
        if limit is not None and count >= limit:
            break
        count += 1
        jobdir.mkdir(parents=True, exist_ok=True)
        selected = [refs[i] for i in job["references"]]
        source, commands = lean_input(job["module"], selected)
        (jobdir / "Check.lean").write_text(source)
        dump(jobdir / "commands.json", commands)
        metadata = dict(module=job["module"], state="started", started=datetime.now(timezone.utc).isoformat(),
                        build_returncode=None, lean_returncode=None)
        dump(metadata_path, metadata)
        source_path = root / selected[0]["source"]
        if selected[0]["source"].startswith("Mathlib/"):
            source_path = root / ".lake/packages/mathlib" / selected[0]["source"]
        if not source_path.is_file():
            metadata["state"] = "source_missing"
        else:
            metadata["state"] = inspect_builds(root, jobdir)
            while metadata["state"] == "build_busy":
                dump(metadata_path, metadata)
                print(f"{job['module']}: waiting for SerrePositivity full build", flush=True)
                time.sleep(10)
                metadata["state"] = inspect_builds(root, jobdir)
        if metadata["state"] != "ready":
            dump(metadata_path, metadata)
            print(f"{job['module']}: {metadata['state']}", flush=True)
            if metadata["state"] in ("preflight_failed", "build_busy"):
                break
            continue
        metadata["source_sha256"] = digest(source_path)
        build = ["zsh", "scripts/refactor/with_build_lock.sh", "--wait", "0", "--", "lake", "build", job["module"]]
        metadata["build_command"] = build
        metadata["build_returncode"] = call(root, build, jobdir / "build.stdout.txt", jobdir / "build.stderr.txt")
        attempt = 0
        while metadata["build_returncode"] == 75:
            attempt += 1
            for stream in ("stdout", "stderr"):
                (jobdir / f"build.{stream}.txt").rename(jobdir / f"build.wait-{attempt}.{stream}.txt")
            print(f"{job['module']}: waiting for build lock", flush=True)
            time.sleep(10)
            while inspect_builds(root, jobdir) == "build_busy":
                time.sleep(10)
            metadata["build_returncode"] = call(root, build, jobdir / "build.stdout.txt", jobdir / "build.stderr.txt")
        if metadata["build_returncode"]:
            metadata["state"] = "build_busy" if metadata["build_returncode"] == 75 else "build_failed"
        else:
            command = ["lake", "env", "lean", "--json", str((jobdir / "Check.lean").relative_to(root))]
            metadata["lean_command"] = command
            metadata["state"] = "checking"
            dump(metadata_path, metadata)
            metadata["lean_returncode"] = call(root, command, jobdir / "lean.stdout.jsonl", jobdir / "lean.stderr.txt")
            metadata["state"] = "checked"
        metadata["finished"] = datetime.now(timezone.utc).isoformat()
        dump(metadata_path, metadata)
        print(f"{job['module']}: {metadata['state']}", flush=True)
        if metadata["state"] == "build_busy":
            break


def parse(directory, plan):
    results = {r["id"]: dict(state="not_run" if r["preparation"] == "ready" else r["preparation"])
               for r in plan["references"]}
    for job in plan["jobs"]:
        jobdir = directory / "modules" / job["module"]
        metadata_path = jobdir / "execution.json"
        if not metadata_path.exists():
            continue
        metadata = json.loads(metadata_path.read_text())
        if metadata["state"] != "checked":
            results.update({i: dict(state=metadata["state"]) for i in job["references"]})
        else:
            commands = json.loads((jobdir / "commands.json").read_text())
            if set(commands) != set(job["references"]):
                raise ValueError(f"command map mismatch: {job['module']}")
            results.update(parse_output((jobdir / "lean.stdout.jsonl").read_text(),
                                        (jobdir / "lean.stderr.txt").read_text(), metadata["lean_returncode"], commands))
    rows = []
    for ref in plan["references"]:
        result = results[ref["id"]]
        rows.append(dict(ref, **result,
                         axioms_json=json.dumps(result.get("axioms"), ensure_ascii=False),
                         extra_axioms_json=json.dumps(result.get("extra_axioms", []), ensure_ascii=False)))
    write_csv(directory / "declaration-results.csv", rows,
              ["id", "raw", "declaration", "source", "source_line", "module", "state", "type",
               "axioms_json", "extra_axioms_json", "axioms_output", "diagnostics"])
    items = []
    for item in plan["items"]:
        states = collections.Counter(results[i]["state"] for i in item["references"])
        state = "no_declarations" if not states else "found" if set(states) == {"found"} else "needs_review"
        extras = sorted({a for i in item["references"] for a in results[i].get("extra_axioms", [])})
        items.append(dict(number=item["number"], status_original=item["status"], state=state,
                          reference_ids=" | ".join(item["references"]),
                          states_json=json.dumps(states, ensure_ascii=False),
                          extra_axioms_json=json.dumps(extras, ensure_ascii=False)))
    write_csv(directory / "item-results.csv", items,
              ["number", "status_original", "state", "reference_ids", "states_json", "extra_axioms_json"])
    summary = dict(references=dict(collections.Counter(r["state"] for r in results.values())),
                   items=dict(collections.Counter(i["state"] for i in items)),
                   nonstandard_axiom_references=sum(bool(r.get("extra_axioms")) for r in results.values()))
    dump(directory / "summary.json", summary)
    print(json.dumps(summary, ensure_ascii=False))
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["prepare", "run", "parse"])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--run-dir", required=True, help="review/check/ 内の相対パス。例 runs/all-01")
    parser.add_argument("--chapter", type=int, action="append", default=[], choices=range(1, 11), help="prepare のみ。省略は全章")
    parser.add_argument("--module", action="append", default=[], help="run のみ。省略は全モジュール")
    parser.add_argument("--limit", type=int, help="run のみ。今回のモジュール数上限")
    parser.add_argument("--resume", action="store_true", help="checked 済みのジョブを飛ばす（raw 出力は上書きしない）")
    args = parser.parse_args()
    root = args.root.resolve()
    base = root / "research/kerodon-coverage/review/check"
    directory = (base / args.run_dir).resolve()
    try:
        if not directory.is_relative_to(base.resolve()) or directory == base.resolve():
            raise ValueError("run-dir は review/check/ の子ディレクトリに限定")
        if args.limit is not None and args.limit < 1:
            raise ValueError("limit は正の整数")
        if args.action != "prepare" and args.chapter:
            raise ValueError("--chapter は prepare 専用")
        if args.action != "run" and (args.module or args.limit is not None or args.resume):
            raise ValueError("--module/--limit/--resume は run 専用")
        if args.action == "prepare":
            prepare(root, directory, set(args.chapter))
            return 0
        plan = json.loads((directory / "plan.json").read_text())
        if plan["schema"] != 1:
            raise ValueError("unsupported plan schema")
        if args.action == "run":
            run(root, directory, plan, set(args.module), args.limit, args.resume)
        summary = parse(directory, plan)
        # 0 は全記載を検査済み・追加公理なし。未実行/未解決を成功にしない。
        return 0 if set(summary["references"]) <= {"found"} and not summary["nonstandard_axiom_references"] else 1
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
