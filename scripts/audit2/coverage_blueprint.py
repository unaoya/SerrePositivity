#!/usr/bin/env python3
"""Generate the blueprint in a separate directory from the audit2 link plan."""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from audit import Failure, ROOT, command, write_json
from coverage import compare, digest, read_baselines, sha
from coverage_verso import BOOKS, is_link_row, name_only, name_only_report, verify_pin

SCRIPTS = ROOT / "blueprint/scripts"
sys.path.insert(0, str(SCRIPTS))
from common import CARD, rendered_links

BASE = Path("blueprint/SerreBlueprint")
JOBS = [("gen_paper.py",), ("gen_cited.py", "clmst", "bs", "vdescent"),
        ("gen_lurie.py", "htt", "ha")] + [
        ("gen_kerodon.py", str(i)) for i in range(1,11)] + [("gen_blueprint.py",)]


def sources():
    for book in sorted(BOOKS):
        folder = ROOT/f"research/{book}-coverage"
        yield from sorted(p for p in folder.iterdir() if p.is_file() and
                          (p.name in {"items.csv","edges.csv","toc.md","statements.csv","item-tags.csv",
                                      "external.csv","route-edges.csv","baseline.csv"}))
        for sub, pattern in (("notes","*.md"), ("review","*.csv")):
            yield from sorted((folder/sub).rglob(pattern) if sub=="notes" else (folder/sub).glob(pattern))
    edge = ROOT/"research/p0-lurie/item-closure/edges.csv"
    if edge.is_file():
        yield edge
    yield from sorted(SCRIPTS.glob("*.py"))
    yield Path(__file__).with_name("coverage_verso.py").resolve()
    yield ROOT / "blueprint/lake-manifest.json"


def status(plan):
    links, problems = {}, []
    for row in plan["references"]:
        if row.get("name") and row["public"]:
            pair = [row["name"], row["module"]]
            if links.setdefault(row["raw"], pair) != pair:
                raise Failure(f"link is inconsistent across sheets: {row['raw']}")
        if is_link_row(row) and (not row.get("name") or not row["public"]):
            problems.append(row)
    return links, problems


def card_label(row):
    number, book = row["item"], row["literature"]
    if row["file"].endswith("/external.csv"):
        cited, _, number = number.partition(" ")
        book = f"ext_{cited}"
    elif number.startswith("(") and book in {"paper", "clmst", "bs", "bs17", "bm18", "rydh"}:
        book += "_eq"
        number = number.strip("()")
    elif number.startswith("Figure ") and book == "paper":
        book += "_fig"
        number = number.split()[-1]
    slug = re.sub(r"[^0-9A-Za-z]+", "_", number).strip("_")
    return f"{book}_{slug}" if slug else book


def verify_output(rows, references):
    expected = {}
    for ref in references:
        if is_link_row(ref):
            names = expected.setdefault(card_label(ref), [])
            if ref.get("name") and ref["public"] and not name_only(ref):
                names.append(ref["name"])
    diffs = [label for label, names in expected.items()
             if label not in rows or rows[label][1] != names]
    diffs.extend(label for label, (_, links) in rows.items() if links and label not in expected)
    if diffs:
        raise Failure(f"planned and generated links differ: {sorted(diffs)[:15]}")


def cards(root):
    rows = {}
    for file in sorted(root.rglob("*.lean")):
        for name, refs in rendered_links(file.read_text()).items():
            if name in rows:
                raise Failure(f"blueprint label appears in two files: {name}")
            rows[name] = [str(file.relative_to(root)), refs]
    return rows


def verify_names(root, references):
    expected = {}
    for ref in references:
        if is_link_row(ref) and ref.get("name") and ref["public"] and name_only(ref):
            expected.setdefault(card_label(ref), []).append(ref["name"])
    found = {}
    for file in root.rglob("*.lean"):
        text = file.read_text()
        starts = list(CARD.finditer(text))
        for i, card in enumerate(starts):
            end = starts[i + 1].start() if i + 1 < len(starts) else len(text)
            names = re.findall(r"^宣言（リンクなし）：(.+)$", text[card.end():end], re.M)
            if names:
                found[card[1]] = re.findall(r"`([^`]+)`", "".join(names))
    if expected != found:
        raise Failure("planned and rendered name-only references differ")


def lean_payload(file):
    """Remove only the generator's provenance prefix when testing for an unchanged chapter."""
    data = file.read_bytes()
    return re.sub(rb"\A-- audit2: [0-9a-f]+ inputs sha256 [0-9a-f]{64}\n"
                  rb"(?:-- audit2 baselines: [0-9a-f, ]+\n)?", b"", data, count=1)


def diff_cards(before, after, plan):
    refs = {}
    for row in plan["references"]:
        refs.setdefault(card_label(row), []).append(row)
    result = []
    for label in sorted(before.keys() | after.keys()):
        a, b = before.get(label), after.get(label)
        if a != b:
            result.append(dict(card=label, before=a, after=b, references=refs.get(label, [])))
    return result


def generate(plan, folder, preview, publish):
    if plan["commit"] != command(["git","rev-parse","HEAD"]):
        raise Failure("blueprint plan is for a different base commit")
    verify_pin(ROOT / "blueprint/lake-manifest.json")
    links, problems = status(plan)
    for file, expected in plan["inputs"].items():
        if sha(ROOT/file) != expected:
            raise Failure(f"stale declaration plan: {file}")
    folder.mkdir(parents=True, exist_ok=True)
    write_json(folder/"unresolved.json", problems)
    shown = name_only_report(plan["references"])
    write_json(folder/"name-only.json", shown)
    if problems and not preview:
        raise Failure(f"{len(problems)} unresolved or non-public blueprint references; see {folder/'unresolved.json'}")
    if preview and publish:
        raise Failure("diagnostic previews cannot be published")
    baselines = list(read_baselines(ROOT))
    baseline_commits = sorted({row["commit"] for row in baselines})
    if not preview:
        check = compare(baselines, plan["references"], {}, strict=True)
        write_json(folder/"baseline-check.json", check)
        if not check["pass_"]:
            raise Failure(f"literature baseline check failed; see {folder/'baseline-check.json'}")
    tree = folder/"tree"
    if tree.exists():
        raise Failure(f"use a new generation output directory: {tree}")
    before = cards(ROOT/BASE)
    (tree/"blueprint").mkdir(parents=True)
    (tree/"research").symlink_to(ROOT/"research", target_is_directory=True)
    shutil.copytree(ROOT/BASE,tree/BASE)
    fingerprints = {p.relative_to(ROOT).as_posix():sha(p) for p in sources()}
    input_hash = digest([plan["commit"], fingerprints, sorted(links.items())])
    wire = folder/"link-plan.json"
    name_only_raw = {r["raw"]: r["name"] for r in plan["references"]
                     if r.get("name") and name_only(r)}
    write_json(wire, dict(root=str(tree.resolve()), commit=plan["commit"], input_hash=input_hash,
                          baseline_commits=baseline_commits, inputs=plan["inputs"], preview=preview,
                          links=links, name_only=name_only_raw))
    start = time.monotonic()
    env = dict(os.environ, AUDIT2_BLUEPRINT_PLAN=str(wire.resolve()))
    with (folder/"generate.log").open("w") as log:
        for name,*args in JOBS:
            subprocess.run([sys.executable, SCRIPTS/name, *args], cwd=tree, env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
    if fingerprints != {p.relative_to(ROOT).as_posix():sha(p) for p in sources()}:
        raise Failure("blueprint inputs changed during rendering")
    after = cards(tree/BASE)
    verify_output(after, plan["references"])
    verify_names(tree/BASE, plan["references"])
    changes = diff_cards(before, after, plan)
    files = {}
    retained = {}
    for f in sorted((tree/BASE).rglob("*")):
        if not f.is_file():
            continue
        rel = f.relative_to(tree/BASE)
        old = ROOT/BASE/rel
        if old.is_file() and sha(f) == sha(old):
            continue
        if old.is_file() and f.suffix == ".lean" and lean_payload(old) == lean_payload(f):
            retained[str(rel)] = sha(old)
        else:
            files[str(rel)] = sha(f)
    write_json(folder/"changes.json", changes)
    result = dict(commit=plan["commit"], preview=preview, input_hash=input_hash, files=files,
                  cards_before=len(before), cards_after=len(after), change_cards=len(changes),
                  linked_before=sum(bool(row[1]) for row in before.values()),
                  linked_after=sum(bool(row[1]) for row in after.values()),
                  missing=len(problems), name_only=shown["count"], retained=retained,
                  seconds=time.monotonic()-start)
    write_json(folder/"result.json", result)
    if publish:
        removed = {p.relative_to(ROOT/BASE) for p in (ROOT/BASE).rglob("*.lean")} - {
            p.relative_to(tree/BASE) for p in (tree/BASE).rglob("*.lean")}
        if removed:
            raise Failure(f"generated files disappeared: {sorted(map(str,removed))}")
        for file in files:
            target = ROOT/BASE/file
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(tree/BASE/file, target)
    print(result["change_cards"], "card changes;", result["missing"], "unresolved links;",
          shown["count"], "displayed by name only")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("plan", type=Path)
    p.add_argument("out", type=Path)
    p.add_argument("--preview", action="store_true")
    p.add_argument("--publish", action="store_true")
    args = p.parse_args()
    out = args.out.resolve()
    if out.is_relative_to(ROOT):
        raise Failure("use an output directory outside the worktree")
    generate(json.loads(args.plan.read_text()), out, args.preview, args.publish)


if __name__ == "__main__":
    try:
        main()
    except (Failure, ValueError, OSError, subprocess.CalledProcessError) as e:
        raise SystemExit(str(e))
