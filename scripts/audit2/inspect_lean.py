#!/usr/bin/env python3
"""Measure unused binders and instance coverage from compiled Lean modules."""
import argparse
from collections import Counter, defaultdict
from pathlib import Path
import json
import subprocess
import sys
import time

from audit import BATCH, LIB, Failure, Run, artifact_path, command, compile_worker, inventory, write_json
from coverage import load_db

INTERFACES = (
    "SerrePositivity.KST.SConstruction.Cofinality.StableWideCofinalitySupply",
    "SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityLaxComparisonInput",
    "SerrePositivity.KST.Fibration.Relative.SingleRelativeComparison",
    "SerrePositivity.KST.NonConnective.DGKappaConeInput",
    "SerrePositivity.KST.NonConnective.DGKappaPerfectInput",
    "SerrePositivity.KST.NonConnective.DGKappaSuspensionRelativeRoofInput",
    "SerrePositivity.KST.NonConnective.DGKappaSplitCofiberInput",
    "SerrePositivity.KST.NonConnective.DGSuspensionNativeActionInput",
    "SerrePositivity.KST.NonConnective.dgKappaNativeBFSquareComparison",
    "SerrePositivity.KST.NonConnective.DGSuspensionStageProvider",
)


def input_paths(sources):
    dependencies = {}
    for lib in map(Path, command(["lake", "env", "printenv", "LEAN_PATH"]).split(":")):
        if lib.resolve() == LIB.resolve():
            continue
        for path in sorted(lib.rglob("*.olean")):
            owner = ".".join(path.relative_to(lib).with_suffix("").parts)
            if owner in sources or (owner in dependencies and dependencies[owner].resolve() != path.resolve()):
                raise Failure(f"ambiguous artifact: {owner}")
            dependencies[owner] = path
    return [("project", m, artifact_path(m)) for m in sorted(sources)] + [
        ("dependency", m, path) for m, path in sorted(dependencies.items())]


def main_dependencies(db):
    todo = ["SerrePositivity.main_statement"]
    seen = set()
    keys = set()
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        for row in db.execute("SELECT module,type_refs,value_refs,ctors FROM decl WHERE name=?", (name,)):
            keys.add((row["module"], name))
            todo.extend(n for column in ("type_refs", "value_refs", "ctors")
                        for n in json.loads(row[column]) if n not in seen)
    return keys


def interfaces(db):
    found = {}
    for name in INTERFACES:
        rows = list(db.execute("SELECT module,kind FROM decl WHERE name=?", (name,)))
        if len(rows) != 1:
            raise Failure(f"missing or ambiguous named interface: {name}")
        found[name] = dict(owner=rows[0]["module"], kind=rows[0]["kind"], typed_uses=[], value_uses=[])
    query = "SELECT module,name,type_refs,value_refs FROM decl"
    for module, name, type_refs, value_refs in db.execute(query):
        for field, refs in (("typed_uses", type_refs), ("value_uses", value_refs)):
            for target in set(json.loads(refs)) & found.keys():
                if name != target:
                    found[target][field].append([module, name])
    return found


def inspect(run, worker, db):
    sources, _ = inventory()
    expected = dict(db.execute("SELECT name,declarations FROM module"))
    if expected.keys() != sources.keys():
        raise Failure("record audit and tracked module populations differ")
    main_keys = main_dependencies(db)
    all_rows = input_paths(sources)
    modules = {}
    primitive = Counter()
    main = Counter()
    instances = defaultdict(set)
    classes = set()
    binders = defaultdict(list)
    unknown_instances = []
    unknown_heads = []
    native_seconds = 0
    with (run.out / "unused-binders.jsonl").open("w") as unused:
        for start in range(0, len(all_rows), BATCH):
            batch = all_rows[start:start + BATCH]
            request = run.lines("inspection-requests.tsv", ["\t".join(map(str, row)) for row in batch])
            raw = run.out / "inspection-chunk.jsonl"
            run.execute(f"inspect-{start // BATCH:03}", [worker, "inspect", request, raw])
            native_seconds += run.receipts[-1]["seconds"]
            with raw.open() as stream:
                for line in stream:
                    mode, owner, *rest = json.loads(line)
                    if mode == "module":
                        if owner in modules:
                            raise Failure(f"duplicate module: {owner}")
                        modules[owner] = rest[0]
                    elif mode == "class":
                        classes.add(rest[0])
                    elif mode == "instance":
                        name, class_name = rest
                        if class_name is None:
                            unknown_instances.append([owner, name])
                        else:
                            instances[class_name].add((owner, name or ""))
                    elif mode == "binders":
                        name, rows = rest
                        key = (owner, name)
                        for index, (binder, in_value, in_type, is_instance, head, dependent) in enumerate(rows):
                            result = ("unknown_value" if in_value is None else
                                      "used_value" if in_value else
                                      "type_only" if in_type else "unused")
                            primitive[result] += 1
                            if key in main_keys:
                                main[result] += 1
                            if in_value is False:
                                unused.write(json.dumps([owner, name, index, binder, in_type, is_instance],
                                                        ensure_ascii=False) + "\n")
                            if is_instance:
                                if head is None:
                                    unknown_heads.append([owner, name, index])
                                else:
                                    binders[head].append([owner, name, index, dependent])
                    else:
                        raise Failure(f"unexpected native result row: {mode}")
    if set(modules) != {owner for _, owner, _ in all_rows} or any(
            modules[m] != count for m, count in expected.items()):
        raise Failure("native artifact population or declaration counts differ")
    if not classes or not instances.keys() <= classes:
        raise Failure("Lean class inventory does not cover all registered instance heads")
    missing = {name: rows for name, rows in sorted(binders.items()) if name in classes and name not in instances}
    unreduced = {name: rows for name, rows in sorted(binders.items()) if name not in classes}
    write_json(run.out / "instance-candidates.json", dict(no_registration_for_head=missing,
               other_unreduced_heads={name: len(rows) for name, rows in unreduced.items()},
               unknown_registration_head=unknown_instances, unknown_binder_head=unknown_heads,
               model_category_with_registered_instances=sorted(instances.get("HomotopicalAlgebra.ModelCategory", ()))))
    uses = interfaces(db)
    write_json(run.out / "unsupplied-interfaces.json", uses)
    return dict(modules=len(expected), dependencies=len(modules) - len(expected),
                declarations=sum(expected.values()), main_dependency_keys=len(main_keys),
                binders=primitive, main_binders=main, instances=sum(map(len, instances.values())),
                distinct_classes=len(classes), missing_classes=len(missing), other_unreduced_heads=len(unreduced),
                unknown_registration_head=len(unknown_instances),
                unknown_binder_head=len(unknown_heads), native_seconds=native_seconds,
                interfaces={n: {k: len(v) for k, v in row.items() if k.endswith("_uses")}
                            for n, row in uses.items()})


def walk(run, worker, db, roots):
    request = run.lines("walk-roots.txt", sorted(set(roots)))
    raw = run.out / "walk.jsonl"
    run.execute("walk-axioms", ["lake", "env", worker, "walk", request, raw])
    with raw.open() as stream:
        mode, imports, import_ms = json.loads(next(stream))
        if mode != "environment":
            raise Failure("missing walk environment receipt")
        observed = {}
        visited = []
        traversal_ms = None
        for line in stream:
            row = json.loads(line)
            if row[0] == "traversal_ms":
                traversal_ms = row[1]
                continue
            owner, name, axioms, count = row
            key = owner, name
            if key in observed:
                raise Failure(f"duplicate walk result: {key}")
            observed[key] = axioms
            visited.append(count)
    expected = {(m, n): sorted(json.loads(a)) for root in roots for m, n, a in db.execute(
        "SELECT module,name,axioms FROM decl WHERE module=?", (root,))}
    changes = [[*k, expected.get(k), observed.get(k)] for k in sorted(observed.keys() | expected.keys())
               if expected.get(k) != observed.get(k)]
    return dict(roots=roots, environment_modules=imports, import_ms=import_ms, traversal_ms=traversal_ms,
                checked=len(observed), record=len(expected), most_constants_per_query=max(visited, default=0),
                native_seconds=run.receipts[-1]["seconds"], differences=changes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("database", type=Path)
    parser.add_argument("out", type=Path)
    parser.add_argument("--walk", action="append", help="walk declared axioms from these module roots")
    args = parser.parse_args()
    started = time.monotonic()
    db = load_db(args.database)
    actual_head = command(["git", "rev-parse", "HEAD"])
    record_head = db.execute("SELECT value FROM metadata WHERE key='head'").fetchone()[0]
    if command(["git", "diff", "--name-only", record_head, "--", "SerrePositivity", "SerrePositivity.lean",
                "lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json"]):
        raise Failure("record and current Lean inputs differ")
    run = Run(args.out)
    worker = compile_worker(run, "Inspection")
    result = walk(run, worker, db, args.walk) if args.walk else inspect(run, worker, db)
    result.update(record_head=record_head, execution_head=actual_head, seconds=time.monotonic() - started)
    write_json(run.out / "result.json", result)
    return int(bool(result.get("differences")))


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (Failure, OSError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
