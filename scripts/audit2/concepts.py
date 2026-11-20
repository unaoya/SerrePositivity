#!/usr/bin/env python3
"""Export audit2 rows in the concept tree's existing dump format."""
import argparse
from collections import defaultdict
from contextlib import ExitStack
from functools import lru_cache
import json
from pathlib import Path
import pickle
import subprocess
import sys

from audit import ROOT, Failure, closure, connect_db, imports_of, write_json


def export(table, output, evidence=None):
    db = connect_db(table)
    graph = imports_of(db)
    if "SerrePositivity" not in graph:
        raise Failure("concept export requires a complete main table")
    reached = closure(graph, ["SerrePositivity"])
    ids = defaultdict(dict)
    for i, (m, n) in enumerate(db.execute("SELECT module,name FROM decl ORDER BY module,name"), 1):
        ids[n][m] = str(i)
    externals = {}
    ambiguities = {}
    by_external_name = defaultdict(set)
    ownership_graph = graph
    if evidence is not None:
        from legacy import external_inventory
        ext_graph, ext_owners = external_inventory(evidence)
        ownership_graph = ext_graph | graph
        for module, rows in ext_owners.items():
            for name, _ in rows:
                by_external_name[name].add(module)

    @lru_cache(maxsize=128)
    def ownership(owner):
        counter = {}
        seen = set()

        def visit(module):
            if module in seen:
                return
            seen.add(module)
            for dep in ownership_graph.get(module, []):
                if dep in ownership_graph:
                    visit(dep)
            counter[module] = len(counter)

        visit(owner)
        return counter

    def split(references, owner):
        ours = []
        outside = []
        for name in references:
            owners = ids.get(name)
            if owners:
                extra = by_external_name.get(name, set())
                if len(owners) == 1 and not extra:
                    m = next(iter(owners))
                else:
                    order = ownership(owner)
                    candidates = owners.keys() | extra
                    options = sorted((order[m], m) for m in candidates if m in order)
                    if not options:
                        outside.append(name)
                        continue
                    m = options[0][1]
                    ambiguities.setdefault((owner, name), m)
                if m in owners:
                    ours.append(owners[m])
                else:
                    outside.append(name)
            else:
                outside.append(name)
        return ours, outside

    output.mkdir(parents=True, exist_ok=False)
    with ExitStack() as stack:
        groups = ("root", "outside")
        fields = ("modules", "decls", "deps", "xdeps", "xnames", "axioms")
        out = {(g, f): stack.enter_context((output / f"{g}.{f}.tsv").open("w"))
               for g in groups for f in fields}

        def emit(field, *row):
            out[group, field].write("\t".join(map(str, row)) + "\n")

        for m, deps in sorted(graph.items()):
            group = "root" if m in reached else "outside"
            emit("modules", m, " ".join(dict.fromkeys(d for d in deps if d in graph)))
        for row in db.execute("SELECT * FROM decl ORDER BY module,name"):
            m, n, kind = row["module"], row["name"], row["kind"]
            group = "root" if m in reached else "outside"
            key = ids[n][m]
            loc = json.loads(row["location"]) if row["location"] else None
            typ, outside_type = split(json.loads(row["type_refs"]), m)
            val, outside_value = split(json.loads(row["value_refs"]), m)
            xids = []
            for x in outside_type:
                if x not in externals:
                    externals[x] = "x" + str(len(externals) + 1)
                    emit("xnames", externals[x], x)
                xids.append(externals[x])
            # The legacy tree reads these columns. Non-theorem Prop and
            # docstring metadata are unavailable in the table and unused by
            # the current tree computation.
            emit("decls", key, n, m, kind, int(bool(json.loads(row["instances"]))),
                 int(kind == "thm"), loc[0] + 1 if loc else 0, loc[2] + 1 if loc else 0,
                 row["internal"], 0, int(row["value_hash"] is not None),
                 len(outside_type), len(outside_value))
            emit("deps", key, " ".join(typ), " ".join(val))
            emit("xdeps", key, " ".join(xids))
            if row["axioms"] is None:
                raise Failure(f"{m}: unknown axioms for {n}")
            direct = sorted(set(json.loads(row["type_refs"]) + json.loads(row["value_refs"]))
                            & set(json.loads(row["axioms"])))
            if direct or kind == "axiom":
                emit("axioms", key, " ".join(direct), kind)
    write_json(output / "owners.json", [[*k, m] for k, m in sorted(ambiguities.items())])


def compatibility_tree(dump):
    # The current assign6 consumer topologically orders the already-folded
    # graph. Folding generated declarations can create cycles. Keep its raw
    # input, and record the back-edges omitted from the compatibility view.
    target = dump.parent
    raw = target / "W-raw.pkl"
    compat = target / "W.pkl"
    external = target / "X.pkl"
    if any(p.exists() for p in (raw, compat, external)):
        raise Failure("choose a fresh concept tree output directory")
    subprocess.run([sys.executable, ROOT / "research/cleanup-zero-base/whole.py", dump, raw],
                   cwd=ROOT, check=True)
    with raw.open("rb") as f:
        data = pickle.load(f)
    nodes = data["N"]
    colors = {}
    removed = []

    def outgoing(name):
        row = nodes[name]
        return iter([(n, "tdeps") for n in sorted(row["tdeps"])] +
                    [(n, "vdeps") for n in sorted(row["vdeps"])])

    for name in sorted(nodes):
        if name in colors:
            continue
        colors[name] = 1
        stack = [(name, outgoing(name))]
        while stack:
            here, edges = stack[-1]
            edge = next(edges, None)
            if edge is None:
                colors[here] = 2
                stack.pop()
                continue
            there, field = edge
            state = colors.get(there, 0)
            if state == 1:
                nodes[here][field].remove(there)
                nodes[there]["users"].remove(here)
                removed.append([nodes[here]["mod"], nodes[here]["name"], field,
                                nodes[there]["mod"], nodes[there]["name"]])
            elif state == 0:
                colors[there] = 1
                stack.append((there, outgoing(there)))

    xnames = {}
    xdeps = {}
    for p in sorted(dump.glob("*.xnames.tsv")):
        with p.open() as f:
            for line in f:
                key, name = line.rstrip("\n").split("\t")
                xnames[key] = name
    for p in sorted(dump.glob("*.xdeps.tsv")):
        with p.open() as f:
            for line in f:
                key, refs = line.rstrip("\n").split("\t")
                if key in nodes:
                    xdeps[key] = tuple(refs.split())
    with compat.open("wb") as f:
        pickle.dump(data, f)
    with external.open("wb") as f:
        pickle.dump((xnames, xdeps), f)
    write_json(target / "compatibility-cycle-edges.json", removed)
    print(f"final compatibility view: {len(nodes)} source rows, {len(removed)} cycle back-edges",
          flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path)
    parser.add_argument("dump", type=Path)
    parser.add_argument("--external-ownership", type=Path, help="stage 1 native external ownership evidence")
    parser.add_argument("--prepare-tree", action="store_true",
                        help="prepare the current assign6-compatible pickles and keep folded back-edges")
    args = parser.parse_args()
    export(args.table, args.dump, args.external_ownership)
    if args.prepare_tree:
        compatibility_tree(args.dump)


if __name__ == "__main__":
    main()
