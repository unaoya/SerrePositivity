#!/usr/bin/env python3
"""Reproduce the IC-2 paper from local Git and Lean source text."""
from collections import Counter, defaultdict, deque
from csv import DictReader, DictWriter, field_size_limit
import json
from pathlib import Path
import re
import subprocess
import sys

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
sys.path[:0] = [str(ROOT / "scripts/refactor"),
                str(ROOT / "evidence/consolidation/organize-einfinity-w1/preparation-code")]
from layer_check import imports, under
from audit_imports import audit_imports
from source_names import declarations

field_size_limit(10000000)
BASE = "1522321e5"
GENERAL = "一般の ∞ 圏論"
PREFIX = "SerrePositivity."
AREAS = ("KST", "HomotopicalAlgebra", "Spectra")


def git(*args, cwd=ROOT):
    return subprocess.check_output(["git", *args], cwd=cwd).decode()


def names(*args, cwd=ROOT):
    return set(git(args[0], "-z", *args[1:], cwd=cwd).strip("\0").split("\0")) - {""}


def read_csv(path):
    with (ROOT / path).open(newline="") as stream:
        return list(DictReader(stream))


def write_csv(path, rows, fields=None):
    with (OUT / path).open("w", newline="") as stream:
        writer = DictWriter(stream, fieldnames=fields or list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def dump(path, data):
    (OUT / path).write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def module(path):
    relative = path.removesuffix(".lean")
    return relative.removeprefix("blueprint/").replace("/", ".")


def local(path):
    return path.endswith(".lean") and "Archive" not in Path(path).parts


# Read only the header. Verso and Lean raw strings in the body do not enter the lexer.
TRIVIA = re.compile(r"\s+|--[^\n]*|/-")
WORD = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*")
HEADER = re.compile(r"(?:(?:public|private|meta)\s+)*import\b")
DELIMITER = re.compile(r"/-|-/")


def header(source):
    def skip(i):
        while match := TRIVIA.match(source, i):
            i = match.end()
            if match[0] == "/-":
                depth = 1
                while depth:
                    nested = DELIMITER.search(source, i)
                    if nested is None:
                        raise ValueError("unclosed header comment")
                    depth += 1 if nested[0] == "/-" else -1
                    i = nested.end()
        return i

    pos = skip(0)
    if (word := WORD.match(source, pos)) and word[0] == "module":
        pos = skip(word.end())
    if (word := WORD.match(source, pos)) and word[0] == "prelude":
        pos = skip(word.end())
    result = []
    while match := HEADER.match(source, pos):
        pos = skip(match.end())
        word = WORD.match(source, pos)
        if word and word[0] == "all":
            pos = skip(word.end())
            word = WORD.match(source, pos)
        if not word:
            raise ValueError("unsupported import after offset " + str(pos))
        result.append(word[0])
        pos = skip(word.end())
    # Cross-check the complete header against the established source scanner.
    assert set(result) == imports(source[:pos]), (result, source[:pos])
    return result


def source_graph(paths, worktree):
    result = {}
    for path in sorted(paths):
        file = worktree / path
        if local(path) and file.is_file():
            try:
                result[path] = header(file.read_text())
            except (ValueError, AssertionError) as exc:
                raise RuntimeError(f"{worktree}/{path}") from exc
    return result


def traverse(roots, graph):
    """Deterministic shortest file-import witness from any listed root."""
    prev = {m: None for m in sorted(roots)}
    queue = deque(prev)
    while queue:
        item = queue.popleft()
        for dep in sorted(graph.get(item, ())):
            if dep in graph and dep not in prev:
                prev[dep] = item
                queue.append(dep)
    return prev


def witness(item, prev):
    if item not in prev:
        return ""
    path = [item]
    while prev[path[-1]] is not None:
        path.append(prev[path[-1]])
    return " → ".join(reversed(path))


def reverse(graph):
    result = defaultdict(set)
    for owner, deps in graph.items():
        for dep in deps:
            result[dep].add(owner)
    return {m: result[m] for m in graph}


def main():
    commit = git("rev-parse", BASE).strip()
    assert subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT).returncode == 0
    assert git("rev-parse", "main").strip() == commit
    tracked = names("ls-files", "--", "*.lean")
    assert not names("diff", "HEAD", "--name-only", "--", "*.lean")
    headers = source_graph(tracked, ROOT)
    paths = {module(p): p for p in headers}
    assert len(paths) == len(headers)
    graph = {module(p): set(deps) for p, deps in headers.items()}
    repository = {m for m in graph if under(m, "SerrePositivity")}

    old = read_csv("research/infinity-outside-map/files.csv")
    assert len({r["path"] for r in old}) == len(old)
    old_paths = {r["path"] for r in old}
    ic1 = read_csv("research/infinity-consolidation-w1/moves.csv")
    oe = json.loads((ROOT / "evidence/consolidation/organize-einfinity-w1/module-map.json").read_text())
    transport = oe | {r["old_module"]: r["new_module"] for r in ic1}
    old_destinations = {new for old_name, new in transport.items() if old_name != new}
    inventory = {p for p in headers if any(p.startswith(f"SerrePositivity/{area}/") for area in AREAS)}
    prior_moves = sorted((inventory - old_paths) & {paths[m] for m in old_destinations if m in paths})
    unknown_new = sorted(inventory - old_paths - set(prior_moves))
    assert not unknown_new, unknown_new
    candidates = {r["module"]: r for r in old if r["classification"] == GENERAL}
    assert len(candidates) == 1725 and set(candidates) <= repository
    assert not set(candidates) & old_destinations
    texts = {m: (ROOT / r["path"]).read_text() for m, r in candidates.items()}
    decls = {m: declarations(text, paths[m]) for m, text in texts.items()}

    entries = {module(p) for p in headers if "/Entrypoints/" in p and p.startswith("SerrePositivity/")}
    sorry_script = ROOT / "scripts/refactor/audit_sorries.lean"
    sorry_seeds = {
        "SerrePositivity.main_statement": "SerrePositivity/Paper/Statement.lean",
        "SerrePositivity.theorem_3_1_K0": "SerrePositivity/Inputs/Descent.lean",
        "SerrePositivity.Section4.supportedRankK0_descent": "SerrePositivity/Paper/Section4/SupportedDescent.lean",
        "SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3":
            "SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean",
    }
    for decl, path in sorry_seeds.items():
        assert decl in sorry_script.read_text()
        assert any(name == decl for name, _, _ in declarations((ROOT / path).read_text(), path))
    a_roots = entries | {"SerrePositivity"} | {module(p) for p in sorry_seeds.values()}
    a = traverse(a_roots, graph)

    review_files = sorted(p for p in names("ls-files", "--", "research")
                          if re.match(r"research/[^/]+-coverage/review/.*\.csv$", p))
    coverage = defaultdict(list)
    missing_coverage, skipped_review = [], []
    selected_statuses = {"own", "partial", "interface"}
    coverage_rows = Counter()
    for file in review_files:
        for row in read_csv(file):
            if "status" not in row and "status_new" not in row:
                skipped_review.append(file)
                break
            status = row.get("status_new") or row.get("status")
            if status not in selected_statuses:
                continue
            coverage_rows[status] += 1
            decl_field = row.get("declarations_new") or row.get("declarations") or ""
            record = dict(review=file, number=row["number"], status=status, declarations=decl_field)
            refs = re.findall(r"((?:SerrePositivity|Mathlib)/[^\s|;@]+?\.lean|SerrePositivity\.lean)", decl_field)
            resolved = set()
            for ref in refs:
                if ref.startswith(("Mathlib/", "SerrePositivity/.lake/packages/mathlib/")):
                    continue
                target = transport.get(module(ref), module(ref))
                if target in graph:
                    resolved.add(target)
                else:
                    missing_coverage.append(record | {"unresolved_path": ref})
            if not refs and decl_field.strip():
                missing_coverage.append(record | {"unresolved_path": ""})
            for target in resolved:
                coverage[target].append(record)
    b = traverse(coverage, graph)

    audits = {module(p.strip()) for p in
              (ROOT / "scripts/refactor/audit_manifest.txt").read_text().splitlines()
              if p.strip() and not p.startswith("#")}
    assert audits <= graph.keys()
    audit_graph = graph | {m: audit_imports((ROOT / paths[m]).read_text()) for m in audits}
    audit_closure = traverse(audits, audit_graph)
    extra_audit_edges = {m: sorted(audit_graph[m] - graph[m]) for m in sorted(audits)
                         if audit_graph[m] - graph[m]}
    docs = traverse({module(p) for p in headers if p.startswith("blueprint/")}, graph)
    drafts = traverse({module(p) for p in headers if p.startswith("formalization-plans/")}, graph)
    all_branch_reports, c_witness, branch_graphs = {}, {}, {}
    worktrees = {}
    for item in git("worktree", "list", "--porcelain").split("\n\n"):
        lines = item.splitlines()
        if lines and lines[-1].startswith("branch refs/heads/"):
            worktrees[lines[-1].removeprefix("branch refs/heads/")] = Path(lines[0].removeprefix("worktree "))
    lanes = {
        "math/inf-supply": ("③-a", None),
        "math/scheme": ("⑥", "72bc75e8b^2"),
        "math/inf-supply-b": ("③-b", "49967c102^2"),
        "research/cited-coverage": ("⑧", None),
        "coord/br54-citation-registry": ("BR54", None),
    }
    for branch, (label, last) in lanes.items():
        ref = subprocess.run(["git", "rev-parse", "--verify", branch], cwd=ROOT, capture_output=True, text=True)
        if ref.returncode:
            assert last
            last_head = git("rev-parse", last).strip()
            assert subprocess.run(["git", "merge-base", "--is-ancestor", last_head, commit], cwd=ROOT).returncode == 0
            all_branch_reports[branch] = dict(label=label, status="ref/worktreeなし・最後の取り込み済み",
                                             last_integrated_head=last_head, roots=[], direct=[], affected=[])
            continue
        head = ref.stdout.strip()
        wt = worktrees.get(branch)
        assert wt
        # Net branch delta + staged/unstaged + nonignored untracked Lean. Files
        # inherited unchanged from the merge base are not branch-specific roots.
        net = names("diff", "--name-only", f"{commit}...{head}", "--", "*.lean")
        dirty = names("diff", "HEAD", "--name-only", "--", "*.lean", cwd=wt)
        untracked = names("ls-files", "--others", "--exclude-standard", "--", "*.lean", cwd=wt)
        touched = net | dirty | untracked
        branch_sources = names("ls-files", "--", "*.lean", cwd=wt) | untracked
        branch_headers = source_graph(branch_sources, wt) if touched else {}
        branch_graph = {transport.get(module(p), module(p)):
                        {transport.get(m, m) for m in deps}
                        for p, deps in branch_headers.items()}
        branch_graphs[branch] = branch_graph
        roots = {transport.get(module(p), module(p)) for p in touched
                 if p in branch_headers and not p.startswith("formalization-plans/")}
        branch_reach = traverse(roots, branch_graph)
        # A current-main closure is also needed when an inherited module on
        # the older branch has since acquired new imports on main.
        current_reach = traverse(roots | set(branch_reach), graph)
        touched_modules = {transport.get(module(p), module(p)): p for p in touched}
        affected, direct = [], []
        for p in sorted(touched & branch_headers.keys()):
            if p.startswith("formalization-plans/"):
                continue
            owner = transport.get(module(p), module(p))
            hits = sorted({transport.get(m, m) for m in branch_headers[p]} & candidates.keys())
            if hits:
                direct.append(dict(path=p, imports=hits, tokens=sum(transport.get(m, m) in candidates for m in branch_headers[p])))
        normalized_roots = set(roots)
        branch_rev = reverse(branch_graph)
        all_dependents = traverse(set(candidates) & branch_graph.keys(), branch_rev)
        for p in sorted(touched & branch_headers.keys()):
            owner = transport.get(module(p), module(p))
            if owner in normalized_roots and owner in all_dependents:
                affected.append(dict(path=p, witness=" → ".join(reversed(witness(owner, all_dependents).split(" → ")))))
        live = label == "③-a" or label in {"⑥", "③-b"} or bool(touched)
        if live:
            for m in sorted(candidates.keys() & (branch_reach.keys() | current_reach.keys())):
                if m in branch_reach:
                    chain = witness(m, branch_reach)
                else:
                    fragment = witness(m, current_reach)
                    head_module = fragment.split(" → ", 1)[0]
                    chain = witness(head_module, branch_reach) + " ⇒main⇒ " + fragment
                c_witness.setdefault(m, []).append({"branch": branch, "witness": chain})
        assert git("rev-parse", branch).strip() == head
        assert names("diff", "HEAD", "--name-only", "--", "*.lean", cwd=wt) == dirty
        assert names("ls-files", "--others", "--exclude-standard", "--", "*.lean", cwd=wt) == untracked
        assert source_graph(touched & branch_headers.keys(), wt) == {p: branch_headers[p] for p in touched & branch_headers.keys()}
        all_branch_reports[branch] = dict(label=label, status="観測済み", head=head, worktree=str(wt),
                                         net_lean=len(net), dirty_lean=sorted(dirty), untracked_lean=sorted(untracked),
                                         roots=sorted(roots), direct=direct, affected=affected,
                                         deleted_or_excluded=sorted(touched - branch_headers.keys()),
                                         phase_c=live, moved_source_edits=sorted(set(touched_modules) & candidates.keys()))
    dump("roots.json", dict(base=commit, root="SerrePositivity", entrypoints=sorted(entries), sorry_sources=sorry_seeds,
                            coverage_sources=coverage, review_csv_count=len(review_files), skipped_review=sorted(set(skipped_review)),
                            coverage_rows=coverage_rows, unresolved_coverage=missing_coverage,
                            formal_audit_modules=sorted(audits), audit_runtime_imports=extra_audit_edges, branch_roots={k: v["roots"] for k, v in all_branch_reports.items()}))
    dump("branch-impact.json", all_branch_reports)
    (Path("/private/tmp/ic2-stage0-intermediate.json")).write_text(json.dumps(dict(
        base=commit, graph={k: sorted(v) for k, v in graph.items()}, paths=paths, headers=headers,
        branch_graphs={k: {m: sorted(ds) for m, ds in g.items()} for k, g in branch_graphs.items()},
        prior_moves=prior_moves, candidates=candidates, declarations=decls,
        a={m: witness(m, a) for m in candidates}, b={m: witness(m, b) for m in candidates}, c=c_witness,
        root_only=sorted(candidates.keys() & traverse({"SerrePositivity"}, graph).keys()), coverage=coverage,
        audit={m: witness(m, audit_closure) for m in candidates}, docs={m: witness(m, docs) for m in candidates},
        drafts={m: witness(m, drafts) for m in candidates}), ensure_ascii=False))
    print("Graph", len(graph), "candidates", len(candidates), "previous moves", len(prior_moves))
    print("Roots", len(a_roots), len(coverage), "unresolved references", len(missing_coverage))
    print("Reached", len(candidates.keys() & a.keys()), len(candidates.keys() & b.keys()), len(c_witness))


if __name__ == "__main__":
    main()
