#!/usr/bin/env python3
"""Read-only BS source structure report; not a Lean proof/axiom audit.

Run from the repository root, or pass --repo. Only local .lean source files are
read; .lake and other hidden/vendor directories are skipped. Import parsing is
limited to Lean headers. All ordinary/public/private imports are dependencies.

Exit 0: structural checks passed (reference warnings may remain).
Exit 1: a local import cycle, unresolved SerrePositivity import, or forbidden
        dependency from an explicitly selected foundation root was found.
Exit 2: invalid configuration or an input could not be read.

Coverage and declaration inventory are advisory. The inventory is deliberately
not an elaborator: generated declarations/instance names, unusual syntax, and
module visibility may be omitted or misclassified. Keep the Lean audits.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import unittest

BS = "SerrePositivity.BhattScholze"
CITATIONS = {
    "andre-relative": BS + ".Inputs.AndreFlatness",
    "b-i-relative": BS + ".Inputs.Perfectoidization",
}
AUDIT_KINDS = {
    "audit_bhatt_scholze.lean": "pure-suite",
    "audit_bhatt_scholze_b4.lean": "pure-suite",
    "audit_bhatt_scholze_refactoring.lean": "pure-suite",
    "audit_bhatt_scholze_andre_conditional.lean": "andre-conditional-suite",
}
DEFAULT_FORBIDDEN = (BS, "SerrePositivity.CLMST", "SerrePositivity.Inputs", "SerrePositivity.Paper")
NOTICE = ("Source/import analysis only. Import coverage and source-name matching do not "
          "establish theorem dependencies, absence of sorry, or successful Lean compilation. "
          "Run the existing Lean proof/axiom audits separately.")
INVENTORY_NOTICE = ("Reference inventory only: explicit named declarations, simple namespace/section "
                    "tracking, and explicit public sections. Generated names and anonymous instances "
                    "are omitted. Unmarked declarations in module files have uncertain visibility. "
                    "No inventory difference changes the exit status.")
COMPONENT = r"(?:«[^»\n]+»|[^\W\d][\w']*)"
NAME = COMPONENT + r"(?:\." + COMPONENT + r")*"
NAME_RE = re.compile(NAME)
MODIFIERS = r"(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|local|scoped)[ \t]+)*"
COMMAND = re.compile(r"^[ \t]*(?P<mods>" + MODIFIERS + r")"
                     r"(?P<kind>namespace|section|mutual|end|theorem|lemma|def|abbrev|opaque|axiom|"
                     r"structure|class|instance)\b", re.M)
RESERVED = {"module", "prelude", "import", "public", "private", "meta", "namespace", "section",
            "end", "universe", "variable", "open", "set_option", "noncomputable", "theorem", "def",
            "abbrev", "instance", "attribute", "class", "structure", "initialize", "syntax", "elab"}


def strip_noncode(text: str) -> str:
    """Mask nested comments and strings, preserving positions and line numbers."""
    out = list(text)
    i, n = 0, len(text)

    def mask(a: int, b: int) -> None:
        for j in range(a, b):
            if text[j] != "\n":
                out[j] = " "

    while i < n:
        if text.startswith("«", i):
            end = text.find("»", i + 1)
            i = n if end < 0 else end + 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
            mask(i, end)
            i = end
        elif text.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            mask(start, i)
        elif text[i] == '"':
            start = i
            i += 1
            while i < n:
                if text[i] == "\\":
                    i = min(i + 2, n)
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            mask(start, i)
        else:
            i += 1
    return "".join(out)


def import_header(text: str) -> list[dict]:
    # One module name belongs to each import, even when split over lines.
    # In particular, arbitrary commands after the header must not be treated
    # as continued imports. This follows Lean.Parser.Module.Syntax's grammar;
    # private import is also recognized for the requested compatibility scan.
    code = strip_noncode(text)
    imports = []
    cursor = 0
    for token in ("module", "prelude"):
        match = re.compile(r"\s*" + token + r"\b").match(code, cursor)
        if match:
            cursor = match.end()
    directive = re.compile(r"\s*(?:(public|private)\s+)?(?:(meta)\s+)?import\s+"
                           r"(?:(all)\s+)?(" + NAME + r")")
    while match := directive.match(code, cursor):
        if match[4] in RESERVED:
            break
        imports.append({"module": match[4], "visibility": match[1] or "ordinary",
                        "meta": bool(match[2]), "all": bool(match[3]),
                        "line": code.count("\n", 0, match.start(4)) + 1})
        cursor = match.end()
    return imports


def mask_attributes(code: str) -> str:
    out = list(code)
    i = 0
    while i < len(code):
        if not code.startswith("@[", i):
            i += 1
            continue
        start, depth = i, 1
        i += 2
        while i < len(code) and depth:
            depth += (code[i] == "[") - (code[i] == "]")
            i += 1
        for j in range(start, i):
            if code[j] != "\n":
                out[j] = " "
    return "".join(out)


def qualify(namespace: str, name: str) -> str:
    if name.startswith("_root_."):
        return name[len("_root_."):]
    return namespace + "." + name if namespace else name


def declarations(text: str, path: str, module: str) -> dict:
    code = mask_attributes(strip_noncode(text))
    visibility = "unspecified-module" if re.search(r"^module\s*$", code, re.M) else "public"
    namespace, stack, found, anonymous = "", [], [], 0
    for command in COMMAND.finditer(code):
        kind, modifiers = command["kind"], command["mods"].split()
        tail = code[command.end():]
        match = NAME_RE.match(tail.lstrip())
        name = match[0] if match else None
        if kind in {"namespace", "section", "mutual"}:
            stack.append((namespace, visibility))
            if kind == "namespace" and name:
                namespace = qualify(namespace, name)
            if "public" in modifiers:
                visibility = "public"
            elif "private" in modifiers:
                visibility = "private"
        elif kind == "end":
            if stack:
                namespace, visibility = stack.pop()
        elif name and name not in RESERVED:
            actual = "private" if "private" in modifiers else "public" if "public" in modifiers else visibility
            found.append({"name": qualify(namespace, name), "kind": kind, "visibility": actual,
                          "path": path, "line": code.count("\n", 0, command.start()) + 1,
                          "module": module})
        elif kind == "instance":
            anonymous += 1
    return {"declarations": found, "anonymous_instances": anonymous}


def listed_assertions(text: str) -> list[str]:
    code = strip_noncode(text)
    return [m[1] for m in re.finditer(r"^[ \t]*assert_no_sorry\s+(" + NAME + r")", code, re.M)]


def lean_sources(root: Path) -> list[Path]:
    files = []
    for base, dirs, names in os.walk(root):
        dirs[:] = sorted(d for d in dirs if not d.startswith(".") and d not in {"node_modules", "__pycache__"})
        files.extend(Path(base) / name for name in sorted(names) if name.endswith(".lean"))
    return sorted(files)


def closure(graph: dict[str, set[str]], roots) -> set[str]:
    seen, todo = set(), list(roots)
    while todo:
        node = todo.pop()
        if node in seen:
            continue
        seen.add(node)
        todo.extend(graph.get(node, ()))
    return seen


def cycle_witnesses(graph: dict[str, set[str]]) -> list[list[str]]:
    color, cycles = {}, []
    for root in sorted(graph):
        if color.get(root):
            continue
        path, position = [root], {root: 0}
        color[root] = 1
        stack = [(root, iter(sorted(graph[root])))]
        while stack:
            node, edges = stack[-1]
            child = next(edges, None)
            if child is None:
                stack.pop()
                color[node] = 2
                position.pop(node)
                path.pop()
            elif color.get(child) == 1:
                cycles.append(path[position[child]:] + [child])
            elif not color.get(child):
                color[child] = 1
                position[child] = len(path)
                path.append(child)
                stack.append((child, iter(sorted(graph.get(child, ())))))
    return cycles


def under(name: str, prefix: str) -> bool:
    return name == prefix or name.startswith(prefix + ".")


def forbidden_path(graph: dict[str, set[str]], root: str, prefixes) -> list[str] | None:
    todo, seen = deque([(root, [root])]), set()
    while todo:
        node, path = todo.popleft()
        if node in seen:
            continue
        seen.add(node)
        if any(under(node, prefix) for prefix in prefixes):
            return path
        todo.extend((child, path + [child]) for child in sorted(graph.get(node, ())))
    return None


def citation_class(reachable: set[str]) -> str:
    kinds = [kind for kind, module in CITATIONS.items() if module in reachable]
    return "+".join(kinds) if kinds else "no-named-bs-citation-import"


def make_report(root: Path, foundation_roots: list[str], forbidden: list[str]) -> dict:
    if not (root / "SerrePositivity" / "BhattScholze").is_dir():
        raise ValueError("--repo must contain SerrePositivity/BhattScholze")
    sources, imports = {}, {}
    for path in lean_sources(root):
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        text = path.read_text(encoding="utf-8")
        sources[module] = (path.relative_to(root).as_posix(), text)
        imports[module] = import_header(text)
    graph = {module: {edge["module"] for edge in edges if edge["module"] in sources}
             for module, edges in imports.items()}
    missing = [{"source": module, **edge} for module, edges in imports.items()
               for edge in edges if under(edge["module"], "SerrePositivity") and edge["module"] not in sources]
    cycles = cycle_witnesses(graph)
    for module in foundation_roots:
        if module not in sources:
            raise ValueError("unknown foundation root: " + module)
    violations = [path for module in foundation_roots if (path := forbidden_path(graph, module, forbidden))]
    bs = {module for module in sources if under(module, BS)}
    categories = {module: citation_class(closure(graph, [module])) for module in sorted(bs)}
    audits, covered, assertions = [], set(), []
    for path in sorted((root / "scripts").glob("audit_bhatt_scholze*.lean")):
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        name_list = listed_assertions(sources[module][1])
        reachable = closure(graph, [module])
        reached_bs = reachable & bs
        covered |= reached_bs
        assertions.extend(name_list)
        audits.append({"path": path.relative_to(root).as_posix(),
                       "suite_category": AUDIT_KINDS.get(path.name, "unclassified-suite"),
                       "direct_bs_imports": sorted(edge["module"] for edge in imports[module] if edge["module"] in bs),
                       "bs_import_closure": sorted(reached_bs),
                       "named_citation_imports": [kind for kind, marker in CITATIONS.items() if marker in reachable],
                       "assert_no_sorry_occurrences": len(name_list),
                       "assert_no_sorry_names": sorted(set(name_list)),
                       "repeated_assertions": {name: count for name, count in sorted(Counter(name_list).items()) if count > 1}})
    inventory, anonymous = [], 0
    for module in sorted(bs):
        path, text = sources[module]
        result = declarations(text, path, module)
        inventory.extend(result["declarations"])
        anonymous += result["anonymous_instances"]
    public = [item for item in inventory if item["visibility"] == "public"]
    public_names, all_source_names, asserted = {d["name"] for d in public}, {d["name"] for d in inventory}, set(assertions)
    warnings = []
    uncovered = sorted(bs - covered)
    if uncovered:
        warnings.append(f"{len(uncovered)} BS modules are outside all dedicated audit import closures; reference warning only.")
    if public_names - asserted:
        warnings.append(f"{len(public_names - asserted)} public source-name candidates lack an assert_no_sorry entry in these BS audits.")
    if not foundation_roots:
        warnings.append("Foundation dependency boundary NOT CHECKED: no --foundation-root was supplied.")
    if not audits:
        warnings.append("No dedicated BS audit files were found.")
    if any(a["suite_category"] == "unclassified-suite" for a in audits):
        warnings.append("An unclassified BS audit is listed; its suite category needs manual review.")
    errors = []
    if cycles:
        errors.append("Local import graph contains a cycle.")
    if missing:
        errors.append("Unresolved SerrePositivity imports were found.")
    if violations:
        errors.append("An explicitly selected foundation root reaches a forbidden module prefix.")
    return {
        "notice": NOTICE, "repository": str(root), "structural_status": "fail" if errors else "pass",
        "errors": errors, "reference_warnings": warnings,
        "graph": {"local_modules": len(sources), "local_edges": sum(map(len, graph.values())),
                  "cycle_witnesses": cycles, "missing_internal_imports": missing,
                  "missing_import_scope": "SerrePositivity only; external package imports are not resolved"},
        "foundation_boundary": {"status": "checked" if foundation_roots else "not-configured",
                                "roots": foundation_roots, "forbidden_prefixes": forbidden, "violation_paths": violations},
        "bs_import_coverage": {"total": len(bs), "covered": len(covered), "uncovered": uncovered,
                               "uncovered_categories": {module: categories[module] for module in uncovered},
                               "citation_classes": {kind: sorted(m for m, k in categories.items() if k == kind)
                                                    for kind in sorted(set(categories.values()))},
                               "classification_note": "Named citation import reachability only; not proof-term purity."},
        "audit_suites": audits,
        "inventory": {"notice": INVENTORY_NOTICE, "named_source_declarations": len(inventory),
                      "public_candidates": len(public), "anonymous_instances_omitted": anonymous,
                      "visibility_counts": dict(sorted(Counter(d["visibility"] for d in inventory).items())),
                      "declarations": inventory,
                      "public_candidates_without_assertion": sorted(public_names - asserted),
                      "asserted_bs_names_not_in_source_inventory": sorted(n for n in asserted - all_source_names if under(n, BS)),
                      "assertions_outside_bs_namespace": sorted(n for n in asserted if not under(n, BS))},
    }


def text_report(report: dict) -> None:
    print(report["notice"])
    graph, coverage = report["graph"], report["bs_import_coverage"]
    print(f"Structural checks: {report['structural_status']}; local modules={graph['local_modules']}, edges={graph['local_edges']}")
    print(f"BS import coverage: {coverage['covered']}/{coverage['total']} (not declaration/proof coverage)")
    for audit in report["audit_suites"]:
        print(f"  {audit['path']} [{audit['suite_category']}]: direct BS={len(audit['direct_bs_imports'])}, "
              f"closure BS={len(audit['bs_import_closure'])}, assert_no_sorry occurrences={audit['assert_no_sorry_occurrences']}, "
              f"citation imports={','.join(audit['named_citation_imports']) or 'none of the named BS inputs'}")
    for module in coverage["uncovered"]:
        print(f"  UNCOVERED [{coverage['uncovered_categories'][module]}] {module}")
    print("Foundation boundary: " + report["foundation_boundary"]["status"])
    inventory = report["inventory"]
    print(f"Reference inventory: public candidates={inventory['public_candidates']}, "
          f"without listed assertion={len(inventory['public_candidates_without_assertion'])}, "
          f"asserted BS names not parsed={len(inventory['asserted_bs_names_not_in_source_inventory'])}")
    print(inventory["notice"])
    for message in report["reference_warnings"]:
        print("WARNING: " + message)
    for message in report["errors"]:
        print("ERROR: " + message)
    for path in graph["cycle_witnesses"] + report["foundation_boundary"]["violation_paths"]:
        print("  " + " -> ".join(path))
    for item in graph["missing_internal_imports"]:
        print(f"  {item['source']}:{item['line']} -> {item['module']}")
    print("Use --json for complete module/name lists and source locations.")


class SelfTests(unittest.TestCase):
    def test_header_and_comment_strings(self):
        source = '''module
/- outer /- import Wrong.Inner -/ import Wrong.Outer -/
public import
  Foo.A
public meta import Foo.B
private import Foo.C
import all Foo.D
import Foo.E

def sample := "import Wrong.String"
import Wrong.AfterCommand
'''
        parsed = import_header(source)
        self.assertEqual([x["module"] for x in parsed], ["Foo.A", "Foo.B", "Foo.C", "Foo.D", "Foo.E"])
        self.assertEqual([x["visibility"] for x in parsed], ["public", "public", "private", "ordinary", "ordinary"])
        self.assertEqual(parsed[2]["line"], 6)
        self.assertTrue(parsed[1]["meta"])
        self.assertTrue(parsed[3]["all"])

    def test_import_header_stops_before_custom_command(self):
        source = "import Mathlib.Util.AssertNoSorry\n\nassert_no_sorry SerrePositivity.Example\nimport Wrong.AfterCommand\n"
        self.assertEqual([x["module"] for x in import_header(source)], ["Mathlib.Util.AssertNoSorry"])

    def test_mask_preserves_lines_and_quoted_names(self):
        source = 'def «a--b» := "namespace Fake\\\"x"\n/- a\n /- b -/ c -/\ntheorem good : True := by trivial\n'
        code = strip_noncode(source)
        self.assertEqual(code.count("\n"), source.count("\n"))
        self.assertIn('«a--b»', code)
        self.assertNotIn('namespace Fake', code)

    def test_inventory_visibility_namespace_attributes_multiline(self):
        source = '''module
@[expose] public noncomputable section
namespace A
@[simp]
theorem
  first : True := by trivial
private lemma hidden : True := by trivial
namespace B
@[attr
  [nested]] public def value := 1
public def _root_.Z.value := 1
end B
instance : Inhabited Nat := inferInstance
local instance namedLocal : Inhabited Nat := inferInstance
end A
end
def uncertain := 1
'''
        result = declarations(source, "Example.lean", "Example")
        names = {x["name"]: x["visibility"] for x in result["declarations"]}
        self.assertEqual(names, {"A.first": "public", "A.hidden": "private", "A.B.value": "public",
                                 "Z.value": "public", "A.namedLocal": "public", "uncertain": "unspecified-module"})
        self.assertEqual(result["anonymous_instances"], 1)

    def test_assertions_comments_multiline_duplicates(self):
        source = 'assert_no_sorry A.first\n-- assert_no_sorry Fake\nassert_no_sorry\n A.first\n#print axioms A.other\n'
        self.assertEqual(listed_assertions(source), ["A.first", "A.first"])

    def test_cycles_and_closure(self):
        graph = {"A": {"B"}, "B": {"C"}, "C": {"B"}, "D": set()}
        self.assertEqual(cycle_witnesses(graph), [["B", "C", "B"]])
        self.assertEqual(closure(graph, ["A"]), {"A", "B", "C"})
        self.assertFalse(cycle_witnesses({"A": {"B"}, "B": set()}))

    def test_foundation_only_selected_roots(self):
        graph = {"Base": {"Helper"}, "Helper": set(), "Connection": {BS + ".X"}, BS + ".X": set()}
        self.assertIsNone(forbidden_path(graph, "Base", [BS]))
        self.assertEqual(forbidden_path(graph, "Connection", [BS]), ["Connection", BS + ".X"])
        self.assertFalse(under(BS + "Else.X", BS))

    def test_citation_categories(self):
        self.assertEqual(citation_class(set()), "no-named-bs-citation-import")
        self.assertEqual(citation_class({CITATIONS["b-i-relative"]}), "b-i-relative")
        self.assertEqual(citation_class(set(CITATIONS.values())), "andre-relative+b-i-relative")

    def test_cli_exit_policies(self):
        with tempfile.TemporaryDirectory(prefix="bs-structure-test-") as directory:
            root = Path(directory)
            bs = root / "SerrePositivity" / "BhattScholze"
            bs.mkdir(parents=True)
            (bs / "A.lean").write_text("namespace SerrePositivity.BhattScholze\ndef sample := 0\nend\n")
            (root / "SerrePositivity" / "Base.lean").write_text("import SerrePositivity.BhattScholze.A\n")
            args = ["--repo", directory, "--json"]

            def run(extra=()):
                with redirect_stdout(io.StringIO()):
                    return main(args + list(extra))

            # Missing audit coverage and declaration assertions are advisory.
            self.assertEqual(run(), 0)
            self.assertEqual(run(["--foundation-root", "SerrePositivity.Base"]), 1)
            (bs / "A.lean").write_text("import SerrePositivity.Base\n")
            self.assertEqual(run(), 1)
            (bs / "A.lean").write_text("import SerrePositivity.DoesNotExist\n")
            self.assertEqual(run(), 1)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--json", action="store_true", help="emit the complete deterministic JSON report")
    parser.add_argument("--foundation-root", action="append", default=[], metavar="MODULE",
                        help="check only explicitly selected roots; repeat for multiple roots")
    parser.add_argument("--forbid-prefix", action="append", metavar="MODULE_PREFIX",
                        help="override default forbidden prefixes for foundation roots; repeat as needed")
    parser.add_argument("--self-test", action="store_true", help="test parsing and structural checks without reading the repo")
    args = parser.parse_args(argv)
    if args.self_test:
        result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(SelfTests))
        return 0 if result.wasSuccessful() else 1
    try:
        report = make_report(args.repo.resolve(), sorted(set(args.foundation_root)),
                             sorted(set(args.forbid_prefix or DEFAULT_FORBIDDEN)))
    except (OSError, UnicodeError, ValueError) as error:
        print("Configuration/read error: " + str(error), file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
    else:
        text_report(report)
    return 1 if report["errors"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
