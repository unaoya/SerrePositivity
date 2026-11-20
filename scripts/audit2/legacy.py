#!/usr/bin/env python3
"""Compare the 76 regional axiom predicates with the pinned stage-1 evidence."""
import argparse
from collections import Counter, defaultdict
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys
import time

from audit import ROOT, Failure, closure, connect_db, imports_of, write_json
from rules import World, check

STANDARD = {"Classical.choice", "Quot.sound", "propext"}
MODEL = "HomotopicalAlgebra.ModelCategory"
MAIN = "SerrePositivity.main_statement"
KAN = "SerrePositivity.Inputs.Homotopy.kanQuillen_model_exists"
BS = "exists_surjective_perfectoidization_of_complete_torsionFree_quotient"
BS_OLD = ["SerrePositivity.BhattScholze.Inputs." + BS,
          "SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_complete_torsionFree_quotient"]
QNAME = r"`+([\w'!?₀-₉]+(?:\.[\w'!?₀-₉]+)*)"


def load(path):
    with gzip.open(path, "rt") as f:
        return json.load(f)


def under(name, prefix):
    return name == prefix or name.startswith(prefix + ".")


def external_inventory(evidence):
    edges = {}
    owners = defaultdict(list)
    data = evidence / "external-owners"
    if not (evidence / "external-attempted.json").is_file():
        raise Failure("stage 1 native external ownership index is required")
    if json.loads((evidence / "external-attempted.json").read_text())["rc"] != 0:
        raise Failure("stage 1 external ownership index did not pass")
    for path in sorted(data.glob("*.tsv")):
        with path.open() as rows:
            for line in rows:
                kind, module, *tail = line.rstrip("\n").split("\t")
                if kind == "import":
                    edges[module] = tail
                elif kind == "owner":
                    owners[module].append((tail[0], tail[1] == "1"))
                else:
                    raise Failure(f"unexpected external index row {kind}")
    if not edges:
        raise Failure("empty external ownership index")
    return edges, owners


def owner_order(graph, roots, candidates):
    visited = set()
    preferred = {}

    def visit(module):
        if module in visited or module not in graph:
            return
        visited.add(module)
        for dep in graph[module]:
            visit(dep)
        for name in candidates.get(module, ()):
            preferred.setdefault(name, module)

    for mod in roots:
        visit(mod)
    return visited, preferred


def allowed_scope(selector, scoped, preferred, rows, public):
    exact = set(selector["exact"])
    prefixes = selector["prefixes"]
    name_prefixes = selector["name_prefixes"]
    picked = set()
    for module in scoped:
        choose_module = module in exact or any(under(module, x) for x in prefixes)
        for name, visible, internal in rows.get(module, ()):
            if preferred.get(name, module) != module or (public and not visible):
                continue
            if selector["kind"] == "explicit":
                if name in exact:
                    picked.add((module, name))
            elif (choose_module and (not selector.get("skip_internal") or not internal)) or any(
                    under(name, q) for q in name_prefixes):
                picked.add((module, name))
    return picked


def validate_receipt(evidence, catalog, name):
    key = hashlib.sha256(name.encode()).hexdigest()[:20]
    receipt = json.loads((evidence / "lean-runs" / (key + ".json")).read_text())
    sha = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    if (receipt["head"] != catalog["head"] or receipt["sha256"] != sha or
            receipt["rc"] != 0 or receipt["path"] != name):
        raise Failure(f"old run does not prove a pass for the same source: {name}")
    log = evidence / receipt["log"]
    if not log.is_file() or "Too many open files in system" in log.read_text(errors="replace"):
        raise Failure(f"missing or invalid old run log: {name}")
    return receipt["log"]


def selectors_for_model(text, choice_by_line):
    # Use the scope of the immediately following collectAxioms call. A later
    # run_cmd can have a different prefix and forbidModel list.
    result = []
    pattern = (r'(?m)^[ \t]*if\s+(.*?)info\.type\.getUsedConstants\.contains\s+`'
               + re.escape(MODEL) + r'\s+then')
    for match in re.finditer(pattern, text):
        line = text.count("\n", 0, match.start()) + 1
        following = [n for n in choice_by_line if n >= line]
        if not following:
            continue
        selected = choice_by_line[min(following)]
        if "forbidModel" in match[1]:
            blocks = list(re.finditer(r'let forbidModel[^\n]*?(?::=\s*)\#\[(.*?)\]', text[:match.start()], re.S))
            if not blocks:
                continue
            modules = set(re.findall(QNAME, blocks[-1][1]))
            selected = {k for k in selected if k[0] in modules}
        result.append(dict(kind="direct-edge", edge="type", forbidden=[MODEL],
                           declarations=sorted(selected)))
    return result


def structural_rules(world, extras):
    return [
        dict(id="old-BS-surjectivity", kind="reachable", starts=[MAIN], forbidden=BS_OLD),
        dict(id="old-KanQuillen", kind="reachable", starts=[MAIN], forbidden=[KAN]),
        dict(id="S1-imports", kind="import-components",
             roots=["SerrePositivity.KST.Fibration.Relative.ClosedStableAll"],
             prefix="SerrePositivity.KST", forbidden=["Cofinality", "NonConnective"]),
        dict(id="K-cofinality-proof", kind="reachable",
             starts=["SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_cofinality"],
             forbidden=[MODEL, "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence"],
             forbidden_modules=["SerrePositivity.KST.Fibration.VerdierKernelEquivalence",
                                "SerrePositivity.KST.NonConnective"]),
        *extras,
    ]


def compare(table, evidence, output):
    output.mkdir(parents=True, exist_ok=True)
    analysis = evidence / "analysis"
    catalog = load(analysis / "catalog.json.gz")
    selectors = load(analysis / "selectors.json.gz")
    order = load(analysis / "import-order.json.gz")["scripts"]
    graph, external = external_inventory(evidence)
    db = connect_db(table)
    current = imports_of(db)
    graph.update(current)
    if set(current) != set(catalog["project"]):
        raise Failure("regional comparison needs the complete pinned stage 1 module population")
    rows = defaultdict(list)
    owners = Counter()
    axioms = {}
    for m, n, public, internal, ax in db.execute("SELECT module,name,public,internal,axioms FROM decl"):
        rows[m].append((n, bool(public), bool(internal)))
        owners[n] += 1
        if ax is None:
            raise Failure(f"unknown axiom result for {m} / {n}")
        axioms[m, n] = set(json.loads(ax))
    external_names = {n for array in external.values() for n, _ in array}
    contested = {n for n, count in owners.items() if count > 1} | external_names
    candidate_maps = []
    for public_only in (False, True):
        candidates = defaultdict(list)
        for m, array in rows.items():
            candidates[m] += [n for n, vis, _ in array if n in contested and (vis or not public_only)]
        for m, array in external.items():
            candidates[m] += [n for n, vis in array if vis or not public_only]
        candidate_maps.append(candidates)
    with gzip.open(analysis / "per-script-sets.json.gz", "rt") as f:
        baselines = [json.loads(line) for line in f]
    summary = []
    union = set()
    extra_rules = []
    diff = []
    migrated = Counter()
    for baseline in baselines:
        file = baseline["path"]
        if not baseline["manifest"]:
            continue
        source = (ROOT / file).read_text()
        old_strict = [tuple(k) for k in baseline["manual"].get("strict_sorry", ())]
        if old_strict:
            validate_receipt(evidence, catalog, file)
            extra_rules.append(dict(id=file + ":strict", kind="strict-sorry", declarations=old_strict))
            migrated["strict_sorry_keys"] += len(old_strict)
        if not baseline["axiom_sites"]:
            continue
        log = validate_receipt(evidence, catalog, file)
        scope = catalog["scripts"][file]
        roots = [entry[0] for entry in order[file]] + scope["runtime"]
        if not re.search(r"(?m)^prelude\s*$", source):
            roots.insert(0, "Init")
        roots += sorted(set(scope["direct"]) - set(roots))
        public = source.lstrip().startswith("module\n") and not re.search(r"(?m)^import all\s+", source)
        reached, preferred = owner_order(graph, roots, candidate_maps[public])
        modules = reached & current.keys()
        got = defaultdict(set)
        choice_by_line = {}
        for selector in selectors[file]:
            allowed = tuple(sorted(selector["axiom_mentions"]))
            chosen = allowed_scope(selector, modules, preferred, rows, public)
            got[allowed].update(chosen)
            choice_by_line[selector["call_line"]] = chosen
        expected = {tuple(a.split(",")): {tuple(k) for k in keys}
                    for a, keys in baseline["axis"].items()}
        report = dict(path=file, old_lean_log=log, kept=0, lost=0, added=0, verdict_difference=0)
        selected = set().union(*got.values()) if got else set()
        for a in sorted(expected.keys() | got.keys()):
            old, new = expected.get(a, set()), got.get(a, set())
            report["kept"] += len(old & new)
            report["lost"] += len(old - new)
            report["added"] += len(new - old)
            union.update(old & new)
            for k in sorted(old - new):
                diff.append([file, *k, "missed target", list(a)])
            for k in sorted(new - old):
                diff.append([file, *k, "extra target", list(a)])
            for k in sorted(old & new):
                if bad := axioms[k] - set(a):
                    diff.append([file, *k, "predicate differs from baseline Lean PASS",
                                 list(a), sorted(axioms[k]), sorted(bad)])
                    report["verdict_difference"] += 1
        for i, rule in enumerate(selectors_for_model(source, choice_by_line)):
            extra_rules.append(dict(id=f"{file}:type-{i}", **rule))
            migrated["type_predicates"] += 1
        if re.search(r'if info\.isAxiom then throwError', source):
            extra_rules.append(dict(id=file + ":no-axiom-kind", kind="forbidden-kind",
                                    declarations=sorted(selected), forbidden=["axiom"]))
            migrated["kind_rules"] += 1
        if 'n.getString! == "ModelCategory"' in source and "info.type.find?" in source:
            extra_rules.append(dict(id=file + ":model-kind", kind="direct-edge", edge="type",
                                    suffixes=["ModelCategory"], forbidden=[], declarations=sorted(selected)))
            migrated["type_suffix_rules"] += 1
        if matches := re.search(r"let allowedFiles[^=]*:=\s*\[(.*?)\]", source, re.S):
            allowed_paths = re.findall(r'"([^"]+)"', matches[1])
            extra_rules.append(dict(id=file + ":direct-sorry-files", kind="direct-sorry-files",
                                    declarations=sorted(selected), allowed=allowed_paths))
            migrated["direct_sorry_file_rules"] += 1
        # Exact modules with recorded declarations were independently expected
        # and visited in the passing old scripts. This complements the set diff.
        expected_modules = set().union(*(set(s["exact"]) for s in selectors[file]
                                         if s["kind"] == "module"))
        exact = {m for m, _ in selected} & expected_modules
        old_exact = {m for ks in expected.values() for m, _ in ks} & expected_modules
        if old_exact:
            extra_rules.append(dict(id=file + ":visited", kind="visited-modules",
                                    expected=sorted(old_exact), actual=sorted(exact)))
            migrated["visited_module_rules"] += 1
        summary.append(report)
    if len(summary) != 76:
        raise Failure(f"expected 76 old regional audits, found {len(summary)}")
    world = World(db)
    compiled_rules = structural_rules(world, extra_rules)
    rule_results = {rule["id"]: check(world, rule) for rule in compiled_rules}
    with gzip.open(output / "regional-rule-specs.json.gz", "wt") as f:
        json.dump(compiled_rules, f, ensure_ascii=False)
    write_json(output / "regions.json", summary)
    write_json(output / "region-differences.json", diff)
    write_json(output / "regional-rules.json", {
        "counts": migrated, "tested": len(rule_results),
        "violations": {k: v for k, v in rule_results.items() if v},
    })
    totals = {k: sum(x[k] for x in summary) for k in ("kept", "lost", "added", "verdict_difference")}
    write_json(output / "legacy-summary.json", dict(rules=len(summary), union=len(union), **totals))
    return bool(diff) or any(rule_results.values())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path)
    parser.add_argument("stage1_evidence", type=Path)
    parser.add_argument("out", type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    result = compare(args.table, args.stage1_evidence, args.out)
    write_json(args.out / "time.json", {"seconds": time.monotonic() - start})
    return result


if __name__ == "__main__":
    sys.exit(main())
