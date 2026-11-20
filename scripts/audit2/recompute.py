#!/usr/bin/env python3
"""Corroborate all declarations, relinquishing the bulk slot after each import."""
import argparse
from collections import Counter
import gzip
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

from audit import (
    ROOT, Failure, FileLimit, Run, assert_stamps, command, compile_worker,
    connect_db, file_stamp, imports_of, inventory, preflight,
    signature, wait_for_resources, write_json,
)

LOCK = ["zsh", "scripts/refactor/with_build_lock.sh", "--class", "bulk", "--"]
IMPORT_LINE = re.compile(r"(?:public )?import [\w\u0080-\uffff]+(?:\.[\w\u0080-\uffff]+)*")


def import_only(path):
    # A conservative source certificate for empty, import-only aggregators.
    # This avoids importing the entire root merely to compare zero declarations.
    sys.path.insert(0, str(ROOT / "scripts/refactor"))
    from layer_check import code_only
    try:
        code = code_only(path.read_text())
    except ValueError:
        return False
    lines = [line.strip() for line in code.splitlines() if line.strip()]
    return bool(lines and lines[0] == "module" and all(IMPORT_LINE.fullmatch(l) for l in lines[1:]))


def prepare(out, table):
    run = Run(out / "prepare")
    sources, _ = inventory()
    db = connect_db(table)
    sig = db.execute("SELECT value FROM metadata WHERE key='signature'").fetchone()[0]
    if sig != signature():
        raise Failure("record table has a different tool or dependency signature")
    graph = imports_of(db)
    if set(graph) != set(sources):
        raise Failure("record table does not cover the full Git inventory")
    reader = compile_worker(run, "Artifacts")
    traces, stamps = preflight(run, sources, sources, reader)
    if traces != dict(db.execute("SELECT name,trace FROM module")):
        raise Failure("record table does not cover the current Lake traces")
    compile_worker(run, "Oracle")
    with gzip.open(out / "stamps.json.gz", "wt") as f:
        json.dump({str(p): list(v) for p, v in stamps.items()}, f)
    empties = [m for m, in db.execute("SELECT name FROM module WHERE declarations=0")
               if import_only(sources[m])]
    write_json(out / "source-empty.json", sorted(empties))
    write_json(out / "prepared.json", dict(signature=sig, table=str(table), stamp=file_stamp(table)))
    run.save_times()


def stable(out, table):
    record = json.loads((out / "prepared.json").read_text())
    if record["table"] != str(table) or record["stamp"] != list(file_stamp(table)):
        raise Failure("record table changed after preflight")
    if record["signature"] != signature():
        raise Failure("toolchain or dependency changed after preflight")
    with gzip.open(out / "stamps.json.gz", "rt") as f:
        stamps = {Path(p): tuple(stamp) for p, stamp in json.load(f).items()}
    assert_stamps(stamps)


def import_group(out, table, number):
    part = out / f"group-{number:03}"
    run = Run(part)
    stable(out, table)
    group = json.loads((part / "plan.json").read_text())
    roots = run.lines("roots.txt", group["roots"])
    wanted = run.lines("wanted.txt", group["targets"])
    result = part / "oracle.jsonl"
    label = f"slow-{number:03}"
    args = ["lake", "env", out / "prepare/Oracle", roots, wanted, result, "all"]
    # The standard estimate already reserves 8,500 external modules.
    # A complete external index already counts those in known_imports.
    known = group["known_imports"]
    estimated_project = (known - 8500 if group.get("external_index_complete") else known) + 2500
    # Leave room for activity in the other slot after the launch-time sample.
    exclusive = known >= (35000 if group.get("external_index_complete") else 18000)
    wait_for_resources(run, label, estimated_project, exclusive=exclusive)
    try:
        run.execute(label, args)
    except Failure as error:
        log = part / (label + ".log")
        spelling = re.search(r"object file '([^']+)' of module .* does not exist",
                             log.read_text(errors="replace"))
        if isinstance(error, FileLimit):
            reason = "enfile"
        elif spelling and Path(spelling[1]).is_file():
            stable(out, table)
            reason = "artifact-lookup"
        else:
            raise
        log.rename(part / (label + f".{reason}.log"))
        wait_for_resources(run, label + "-retry", estimated_project, exclusive=True)
        run.execute(label + "-retry", args)
    stable(out, table)
    write_json(part / "complete.json", dict(stamp=file_stamp(result), targets=len(group["targets"])))


def pack_groups(graph, targets, limit):
    nodes = set(graph)
    for deps in graph.values():
        nodes.update(deps)
    index = {n: 1 << i for i, n in enumerate(sorted(nodes))}
    masks = {}

    def reach(module):
        if module not in masks:
            mask = index[module]
            for dep in graph.get(module, []):
                mask |= reach(dep)
            masks[module] = mask
        return masks[module]

    needed = set(targets)
    sizes = {m: reach(m).bit_count() for m in needed}
    components = {m: m.split(".") for m in needed}
    groups = []
    while needed:
        seed = max(needed, key=lambda m: (sizes[m], m))

        def family(module):
            common = 0
            for left, right in zip(components[seed], components[module]):
                if left != right:
                    break
                common += 1
            return common, sizes[module], module

        roots = []
        imported = 0
        for module in sorted(needed, key=family, reverse=True):
            if imported & index[module]:
                continue
            merged = imported | masks[module]
            if roots and merged.bit_count() > limit:
                continue
            roots.append(module)
            imported = merged
            if len(roots) == 2500:
                break
        covered = sorted(m for m in needed if imported & index[m])
        needed.difference_update(covered)
        groups.append(dict(roots=roots, targets=covered, known_imports=imported.bit_count()))
    return groups


def grouped_compare(out, table, limit, external_evidence, replan):
    out.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()

    def locked(action, *args):
        env = {**os.environ, "AUDIT2_QUEUED_AT": str(time.time())}
        subprocess.run([*LOCK, sys.executable, __file__, str(out), str(table),
                        "--action", action, *args], cwd=ROOT, env=env, check=True)

    if not (out / "prepared.json").exists():
        locked("prepare")
    stable(out, table)
    db = connect_db(table)
    graph = imports_of(db)
    sources, _ = inventory()
    empty = set(json.loads((out / "source-empty.json").read_text()))
    if not empty <= sources.keys():
        raise Failure("empty-module proof contains untracked modules")
    plans = out / "plans.json"
    existing = json.loads(plans.read_text()) if plans.exists() else None
    if existing is None or replan:
        kept = []
        if existing is not None:
            for number, group in enumerate(existing):
                part = out / f"group-{number:03}"
                if (part / "complete.json").exists():
                    if len(kept) != number:
                        raise Failure("cannot replan around a noncontiguous completed sequence")
                    kept.append(group)
                elif part.exists():
                    part.rename(out / f"earlier-{int(time.time())}-group-{number:03}")
        complete_ext = False
        if external_evidence is not None:
            from legacy import external_inventory, load
            previous = load(external_evidence / "analysis/catalog.json.gz")["head"]
            changed = command(["git", "diff", "--name-only", previous, "HEAD",
                               "--", "lean-toolchain", "lake-manifest.json", "lakefile.toml"])
            if changed:
                raise Failure("external import index has a different pinned dependency configuration")
            external, _ = external_inventory(external_evidence)
            graph = external | graph
            absent = {n for ds in graph.values() for n in ds if n not in graph}
            if absent:
                raise Failure(f"external import index misses {len(absent)} graph nodes")
            complete_ext = True
        done = {m for group in kept for m in group["targets"]}
        rest = pack_groups(graph, sources.keys() - empty - done, limit)
        for group in rest:
            group["external_index_complete"] = complete_ext
        groups = kept + rest
        write_json(plans, groups)
    else:
        groups = existing
    expected_modules = sources.keys() - empty
    assigned = [m for group in groups for m in group["targets"]]
    if len(assigned) != len(set(assigned)) or set(assigned) != expected_modules:
        raise Failure("group plan does not partition the non-empty source-module roster")
    for number, group in enumerate(groups):
        part = out / f"group-{number:03}"
        part.mkdir(exist_ok=True)
        write_json(part / "plan.json", group)
        receipt = part / "complete.json"
        if not receipt.exists():
            locked("import", "--number", str(number))
        observed = json.loads(receipt.read_text())
        if observed["stamp"] != list(file_stamp(part / "oracle.jsonl")) or observed["targets"] != len(group["targets"]):
            raise Failure(f"group {number}: output changed since measurement")

    expected_by_module = Counter()
    expected = {}
    for m, n, axs in db.execute("SELECT module,name,axioms FROM decl"):
        expected_by_module[m] += 1
        expected[m, n] = None if axs is None else set(json.loads(axs))
    if empty & expected_by_module.keys():
        raise Failure("a source-certified empty module has records in the table")

    seen = set()
    modules = set(empty)
    modes = Counter()
    differences = []
    for number, group in enumerate(groups):
        own = set(group["targets"])
        headers = {}
        observed_counts = Counter()
        rows = out / f"group-{number:03}/oracle.jsonl"
        with rows.open() as f:
            for line in f:
                row = json.loads(line)
                m = row[0]
                if m not in own:
                    differences.append([m, None, "unexpected module", number])
                    continue
                if len(row) == 2:
                    if m in headers or m in modules:
                        differences.append([m, None, "repeated module header", number])
                    headers[m] = row[1]
                    modules.add(m)
                    continue
                _, n, axs, mode = row
                key = m, n
                observed_counts[m] += 1
                if key not in expected or key in seen:
                    differences.append([m, n, "extra or repeated declaration", number])
                    continue
                seen.add(key)
                modes[mode] += 1
                old = expected[key]
                if old != set(axs):
                    differences.append([m, n, None if old is None else sorted(old), sorted(set(axs)), mode])
        for m in sorted(own):
            if headers.get(m) != observed_counts[m] or observed_counts[m] != expected_by_module[m]:
                differences.append([m, None, "module count", headers.get(m), observed_counts[m], expected_by_module[m]])
    stable(out, table)
    missing = sorted(expected.keys() - seen)
    result = dict(pass_=not missing and not differences and modules == set(sources),
                  expected=len(expected), compared=len(seen), modules=len(modules),
                  source_empty_modules=len(empty), import_groups=len(groups),
                  oracle_modes=modes, missing=missing, differences=differences)
    write_json(out / "comparison.json", result)
    write_json(table.parent / "corroboration.json",
               dict(pass_=result["pass_"], evidence=str(out / "comparison.json")))
    timed = [json.loads(p.read_text()) for p in sorted(out.glob("*/timings.json"))]
    write_json(out / "timings.json", dict(wait=sum((r["wait"] or 0) for r in timed),
        elapsed=time.monotonic() - start, jobs=[j for r in timed for j in r["jobs"]]))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("out", type=Path)
    parser.add_argument("table", type=Path)
    parser.add_argument("--limit", type=int, default=16500)
    parser.add_argument("--external-ownership", type=Path,
                        help="same-version complete external import index for sizing groups")
    parser.add_argument("--replan", action="store_true", help="regroup unfinished imports with the supplied budget")
    parser.add_argument("--action", choices=("prepare", "import"))
    parser.add_argument("--number", type=int)
    args = parser.parse_args()
    out, table = args.out.resolve(), args.table.resolve()
    if args.limit < 1:
        parser.error("--limit must be positive")
    if args.action == "prepare":
        prepare(out, table)
    elif args.action == "import":
        import_group(out, table, args.number)
    else:
        return 0 if grouped_compare(out, table, args.limit, args.external_ownership, args.replan)["pass_"] else 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (Failure, OSError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        sys.exit(2)
