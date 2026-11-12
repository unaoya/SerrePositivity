#!/usr/bin/env python3
"""Check the five KL-W1 tiers on a tracked Lean import graph."""

import argparse
from graphlib import CycleError, TopologicalSorter
import json
from pathlib import Path
import re
import subprocess

from layer_check import code_only, under


TIERS = ("SharedFoundation", "Portable", "Comparison", "Entrypoints", "Consumers")
IC = "SerrePositivity.InfinityCategories"
IMPORT = re.compile(
    r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\s+(?:all\s+)?"
    r"([^\W\d][\w']*(?:\.[^\W\d][\w']*)*)", re.M,
)


def source_graph(root, excluded):
    paths = subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"], cwd=root)
    graph = {}
    for name in paths.decode().split("\0"):
        if not name:
            continue
        path = Path(name)
        module = ".".join(path.with_suffix("").parts)
        if any(under(module, prefix) for prefix in excluded):
            continue
        graph[module] = set(IMPORT.findall(code_only((root / path).read_text())))
    return graph


def exceptions(rows, graph):
    result = {}
    for row in rows:
        edge = row["from"], row["to"]
        if edge in result or not row["reason"].strip():
            raise ValueError(f"duplicate or unexplained exception: {edge}")
        if edge[0] not in graph or edge[1] not in graph[edge[0]]:
            raise ValueError(f"stale exception: {edge}")
        result[edge] = row["reason"]
    return result


def check(graph, config):
    if config["schema_version"] != 1:
        raise ValueError("expected schema_version 1")
    explicit = config["modules"]
    if set(explicit) - graph.keys() or set(explicit.values()) - set(TIERS):
        raise ValueError("unknown module or tier in modules")
    unknown = sorted(m for m in graph if under(m, IC) and m not in explicit)
    if unknown:
        raise ValueError(f"missing per-file tier ({len(unknown)}): {unknown[:10]}")
    tier = {m: explicit.get(m, "Consumers") for m in graph}
    ranks = {name: i for i, name in enumerate(TIERS)}
    implementation = tuple(config["implementation_prefixes"])
    foreign = tuple(config["external_prefixes"])
    if any(under(pref, "SerrePositivity") or under("SerrePositivity", pref) for pref in foreign):
        raise ValueError("project imports cannot be marked external")
    prefixes = {
        prefix: tuple(number)
        for prefix, number in config["sections"].items()
    }
    if any(len(pair) != 2 or any(type(n) is not int or n <= 0 for n in pair)
           for pair in prefixes.values()):
        raise ValueError("sections must map path prefixes to [chapter, section]")

    def section(module):
        return next((prefixes[p] for p in sorted_prefixes if under(module, p)), None)

    sorted_prefixes = sorted(prefixes, key=len, reverse=True)
    sections = {m: section(m) for m in graph}
    missing = sorted(m for m in graph if under(m, IC + ".Kerodon") and not sections[m])
    if missing:
        raise ValueError(f"missing Kerodon section ({len(missing)}): {missing[:10]}")
    boundaries = exceptions(config.get("implementation_edges", []), graph)
    reverse = exceptions(config.get("reverse_edges", []), graph)
    used_boundaries, used_reverse = set(), set()
    report = {"violations": [], "approved_reverse_edges": [], "modules": len(graph)}
    problems = report["violations"]

    def issue(kind, *path):
        problems.append({"kind": kind, "path": path})

    local = {p: sorted(graph[p] & graph.keys()) for p in sorted(graph)}
    for p, imports in local.items():
        for dep in sorted(graph[p] - graph.keys()):
            if not any(under(dep, pref) for pref in foreign):
                issue("unresolved-import", p, dep)
        for dep in imports:
            edge = p, dep
            a, b = tier[p], tier[dep]
            in_implementation = any(under(dep, pref) for pref in implementation)
            needs_boundary = a == "Comparison" and (b == "Consumers" or in_implementation)
            approved = needs_boundary and in_implementation and b != "Entrypoints" and edge in boundaries
            if approved:
                used_boundaries.add(edge)
            elif needs_boundary:
                issue("implementation-boundary", *edge)
            if ranks[a] < ranks[b] and not (approved and b == "Consumers"):
                issue("tier-order", *edge)
            if sections[p] and sections[dep] and sections[p] < sections[dep]:
                if edge in reverse:
                    used_reverse.add(edge)
                    report["approved_reverse_edges"].append({"path": edge, "reason": reverse[edge]})
                else:
                    issue("reverse-section", *edge)
    for edge in sorted(boundaries.keys() - used_boundaries):
        issue("unused-implementation-exception", *edge)
    for edge in sorted(reverse.keys() - used_reverse):
        issue("unused-reverse-exception", *edge)
    try:
        order = list(TopologicalSorter(local).static_order())
    except CycleError as error:
        issue("import-cycle", *error.args[1])
        return report

    # Imports precede their importers. Store one deterministic witness per node.
    blocked = {}
    for p in order:
        if any(under(p, pref) for pref in implementation):
            blocked[p] = None
        else:
            witness = next((dep for dep in local[p] if dep in blocked), None)
            if witness is not None:
                blocked[p] = witness
        if tier[p] in ("SharedFoundation", "Portable") and p in blocked:
            path = [p]
            while blocked[path[-1]] is not None:
                path.append(blocked[path[-1]])
            issue("portable-implementation-closure", *path)
    report["topological_order"] = order
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--config", type=Path, required=True)
    args = parser.parse_args()
    try:
        config = json.loads(args.config.read_text())
        config = config.get('klw1', config)
        report = check(source_graph(args.root, config.get("exclude_prefixes", [])), config)
    except (KeyError, ValueError, OSError) as error:
        parser.exit(2, f"{error}\n")
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return int(bool(report["violations"]))


if __name__ == "__main__":
    raise SystemExit(main())
