"""Unit and optional Lean integration tests for the KL-W1 migration tools."""

import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch
from contextlib import redirect_stderr
from io import StringIO

from klw1_layer_check import check
from klw1_namespace import Migration, checked_capture, collect, module_name, render_aliases, rewrite, select_aliases
from klw1_review_assignment import check_review_gate, load_reviews, refresh, toc_sections


def occurrence(data, token, old, owner, kind="term", start=0):
    a = data.encode().index(token.encode(), start)
    return {"start": a, "stop": a + len(token.encode()), "name": old, "module": owner,
            "kind": kind, "namespace": "[anonymous]"}


class NamespaceTests(unittest.TestCase):
    def test_rewrite_uses_resolution_and_byte_offsets(self):
        text = '-- 日本語 Old.f\npublic meta import\n  OldModule\ndef use (f : Nat) := Old.f + f\n'
        ref = occurrence(text, "Old.f", "Old.f", "OldModule", start=text.encode().index(b"def use"))
        plan = Migration({"rows": [{"module": "OldModule", "old": "Old.f", "new": "New.f"}],
                          "modules": {"OldModule": "NewModule"}})
        result, issues = rewrite({"module": "Use", "source": text, "refs": [ref], "commands": []}, plan)
        self.assertEqual(issues, [])
        self.assertEqual(result.decode(), text.replace("  OldModule", "  NewModule")
                         .replace(":= Old.f", ":= _root_.New.f"))

    def test_shared_spelling_rewrites_by_owner_and_rejects_alias_collision(self):
        plan = Migration({"rows": [
            {"module": "OldA", "old": "Old.f", "new": "NewA.f"},
            {"module": "OldB", "old": "Old.f", "new": "NewB.f"},
        ]})
        scopes = []
        for owner, destination in (("OldA", b"_root_.NewA.f"), ("OldB", b"_root_.NewB.f")):
            data = {"module": "Use" + owner, "source": "Old.f", "commands": [],
                    "refs": [occurrence("Old.f", "Old.f", "Old.f", owner)]}
            self.assertEqual(rewrite(data, plan), (destination, []))
            scopes.append((owner, owner + ".lean", data))
        with self.assertRaisesRegex(ValueError, "separate the scopes"):
            select_aliases(scopes, plan)

    def test_removes_only_the_obsolete_plain_open(self):
        plan = Migration({"rows": [{"module": "A", "old": "Old.f", "new": "New.f"}],
                          "opens": {"Old": None}})
        for args, prefix in (("Old", ""), ("Old Keep", "open Keep"), ("Keep Old", "open Keep")):
            text = "open " + args + "\n#check f\n"
            stop = text.index("\n")
            commands = [
                {"kind": "open", "start": text.index(arg), "stop": text.index(arg) + len(arg),
                 "mode": "simple", "names": [arg], "command": {"start": 5, "stop": stop}}
                for arg in args.split()
            ]
            ref = occurrence(text, "f", "Old.f", "A", start=stop)
            result, issues = rewrite({"module": "Use", "source": text, "refs": [ref],
                                      "commands": commands}, plan)
            self.assertEqual(issues, [])
            self.assertEqual(result, (prefix + "\n#check _root_.New.f\n").encode())

        text = "open scoped Old"
        command = {"kind": "open", "start": 12, "stop": 15, "mode": "scoped",
                   "names": ["Old"], "command": {"start": 5, "stop": 15}}
        result, issues = rewrite({"module": "Use", "source": text, "refs": [],
                                  "commands": [command]}, plan)
        self.assertIsNone(result)
        self.assertIn("obsolete namespace", issues[0]["reason"])

    def test_removed_open_qualifies_unmoved_relative_names(self):
        text = "open Old\n#check Realization.functor\n"
        ref = occurrence(text, "Realization.functor", "Old.Realization.functor", "Retained")
        command = {"kind": "open", "start": 5, "stop": 8, "mode": "simple", "names": ["Old"],
                   "command": {"start": 5, "stop": 8}}
        rendered, issues = rewrite({"module": "Uses", "source": text, "refs": [ref],
                                    "commands": [command]}, Migration({"rows": [], "opens": {"Old": None}}))
        self.assertEqual(issues, [])
        self.assertEqual(rendered, b"\n#check _root_.Old.Realization.functor\n")

    def test_competing_resolutions_block_the_entire_file(self):
        ref = occurrence("same", "same", "Old.same", "OldModule")
        local = {**ref, "kind": "local", "name": "", "module": ""}
        plan = Migration({"rows": [{"module": "OldModule", "old": "Old.same", "new": "New.same"}]})
        result, issues = rewrite({"module": "Use", "source": "same", "refs": [ref, local], "commands": []}, plan)
        self.assertIsNone(result)
        self.assertTrue(issues)

    def test_alias_use_requires_external_resolution_and_orders_selected_types(self):
        owner = "SerrePositivity.InfinityCategories.OldModule"
        plan = Migration({"rows": [
            {"module": owner, "old": "Old.f", "new": "New.f", "type_dependencies": ["Old.Box"]},
            {"module": owner, "old": "Old.Box", "new": "New.Box"},
            {"module": owner, "old": "Old.unused", "new": "New.unused"},
        ], "modules": {owner: "SerrePositivity.InfinityCategories.NewModule",
                        "SerrePositivity.KST.Moving": "SerrePositivity.InfinityCategories.Moved"},
            "existing_aliases": {"Past.f": "Old.f"}})
        refs = [occurrence(n, n, n, owner) for n in ("Old.f", "Old.Box", "Past.f")]
        inside = occurrence("Old.unused", "Old.unused", "Old.unused", owner)
        entries = [
            ("main", "KST.lean", {"module": "SerrePositivity.KST", "refs": refs}),
            ("branch", "drafts/F.lean", {"module": "drafts.F", "refs": refs[:1]}),
            ("main", "Internal.lean", {"module": owner, "refs": [inside]}),
            ("main", "KST/Moving.lean", {"module": "SerrePositivity.KST.Moving", "refs": [inside]}),
        ]
        selected, existing = select_aliases(entries, plan)
        self.assertEqual(set(selected), {"Old.f", "Old.Box"})
        self.assertEqual(len(selected["Old.f"]["uses"]), 2)
        self.assertEqual(set(existing), {"Past.f"})
        output = render_aliases(selected, plan, "F2.DeprecatedAlias", "2026-11-07")
        self.assertLess(output.index("_root_.Old.Box"), output.index("_root_.Old.f"))
        self.assertNotIn("unused", output)
        self.assertNotIn("Past.f", output)

    def test_qualified_name_in_unindexed_syntax_is_blocked(self):
        plan = Migration({"rows": [{"module": "Old", "old": "Old.f", "new": "New.f"}]})
        result, issues = rewrite({"module": "Use", "source": "macroInput Old.f\n",
                                  "refs": [], "commands": []}, plan)
        self.assertIsNone(result)
        self.assertIn("no semantic source span", issues[0]["reason"])

    def test_field_receiver_and_method_can_have_different_owners(self):
        text = "x.step"
        ref = occurrence(text, "step", "Old.Record.step", "Method", kind="field")
        plan = Migration({"rows": [
            {"module": "TypeOwner", "old": "Old.Record", "new": "New.Record"},
            {"module": "Method", "old": "Old.Record.step", "new": "New.Record.step"},
        ]})
        rendered, issues = rewrite({"module": "Uses", "source": text, "refs": [ref], "commands": []}, plan)
        self.assertEqual(issues, [])
        self.assertEqual(rendered, b"x.step")

    def test_unmoved_extension_on_a_renamed_type_requires_review(self):
        text = "r.collapseRelative"
        ref = occurrence(text, "collapseRelative", "Old.Record.collapseRelative", "Consumer", kind="field")
        plan = Migration({"rows": [
            {"module": "TypeOwner", "old": "Old.Record", "new": "New.Record"},
        ]})
        rendered, issues = rewrite({"module": "Uses", "source": text, "refs": [ref], "commands": []}, plan)
        self.assertIsNone(rendered)
        self.assertIn("unmoved extension on renamed receiver", issues[0]["reason"])

    def test_unmapped_member_of_renamed_declaration_requires_review(self):
        plan = Migration({"rows": [
            {"module": "TypeOwner", "old": "Old.Record", "new": "New.Record"},
            {"module": "TypeOwner", "old": "Old.f", "new": "New.f"},
        ]})
        for text, owner, indexed in (("Old.Record.mk", "TypeOwner", True),
                                      ("Old.Record.mk", "TypeOwner", False),
                                      ("Old.f_assoc", "TypeOwner", True),
                                      ("Old.f_assoc", "TypeOwner", False)):
            refs = [occurrence(text, text, text, owner)] if indexed else []
            rendered, issues = rewrite({"module": "Uses", "source": text,
                                        "refs": refs, "commands": []}, plan)
            self.assertIsNone(rendered)
            self.assertTrue(issues)
        # A retained external method remains callable by its original full name.
        text = "Old.Record.retained"
        ref = occurrence(text, text, text, "ExternalOwner")
        rendered, issues = rewrite({"module": "Uses", "source": text,
                                    "refs": [ref], "commands": []}, plan)
        self.assertEqual(issues, [])
        self.assertEqual(rendered, text.encode())

    def test_projection_suffix_has_separate_semantic_span(self):
        text = "#check Old.functor.map\n"
        refs = [occurrence(text, "Old.functor", "Old.functor", "Owner"),
                occurrence(text, "map", "CategoryTheory.Functor.map", "Mathlib", kind="field")]
        plan = Migration({"rows": [
            {"module": "Owner", "old": "Old.functor", "new": "New.functor"},
        ]})
        rendered, issues = rewrite({"module": "Uses", "source": text,
                                    "refs": refs, "commands": []}, plan)
        self.assertEqual(issues, [])
        self.assertEqual(rendered, b"#check _root_.New.functor.map\n")
        # Without the suffix reference, custom syntax must still be reviewed.
        rendered, issues = rewrite({"module": "Uses", "source": text,
                                    "refs": refs[:1], "commands": []}, plan)
        self.assertIsNone(rendered)
        self.assertIn("no semantic source span", issues[0]["reason"])

    def test_unresolved_relative_open_with_migration_policy_is_reviewed(self):
        plan = Migration({"rows": [], "opens": {"IC.DGNerve": None}})
        for text, first, last, blocked in (("open IC DGNerve\n", "IC", "DGNerve", True),
                                            ("open CategoryTheory Limits\n", "CategoryTheory", "Limits", False)):
            stop = len(text.rstrip())
            commands = [{"kind": "open", "start": text.index(name),
                         "stop": text.index(name) + len(name), "mode": "simple",
                         "names": [name] if name == first else [],
                         "command": {"start": 5, "stop": stop}}
                        for name in (first, last)]
            rendered, issues = rewrite({"module": "Uses", "source": text,
                                        "refs": [], "commands": commands}, plan)
            if blocked:
                self.assertIsNone(rendered)
                self.assertIn("could not be resolved", issues[0]["reason"])
            else:
                self.assertEqual(issues, [])
                self.assertEqual(rendered, text.encode())

    def test_published_partial_namespace_policies_keep_actual_namespaces(self):
        plan = json.loads((Path(__file__).parent / "targets/kl-namespace-map.json").read_text())
        for name in ("SerrePositivity.SimplicialModel", "SerrePositivity.HomotopyFunctionComplex"):
            self.assertEqual(plan["opens"][name], name)
        self.assertIsNone(plan["module_opens"]["SerrePositivity.EInfinity.BarrattEccles.Theory.EnrichedPointPrecomposition"]["SerrePositivity.KST.Comparison"])

    def test_module_open_policy_keeps_other_consumers_and_qualifies_retained_names(self):
        text = "open Old\n#check retained\n#check moved\n"
        plan = Migration({"rows": [{"module": "Owner", "old": "Old.moved", "new": "New.moved"}],
                          "opens": {"Old": "Old"}, "namespaces": {"Owner": {"Old": "New"}},
                          "module_opens": {"NewConsumer": {"Old": None}}})
        data = {"module": "OldConsumer", "source": text, "refs": [occurrence(text, "retained", "Old.retained", "Unmoved"), occurrence(text, "moved", "Old.moved", "Owner")],
                "commands": [{"kind": "open", "mode": "simple", "names": ["Old"], "start": 5, "stop": 8, "command": {"start": 5, "stop": 8}}]}
        rendered, issues = rewrite(data, plan)
        self.assertEqual(issues, [])
        self.assertEqual(rendered, b"open Old\n#check retained\n#check _root_.New.moved\n")
        rendered, issues = rewrite(data | {"module": "NewConsumer"}, plan)
        self.assertEqual(issues, [])
        self.assertEqual(rendered, b"\n#check _root_.Old.retained\n#check _root_.New.moved\n")

    def test_detached_method_adds_a_name_resolution_export(self):
        text = "def Old.Record.step (n : Nat) := n + 1\n"
        ref = occurrence(text, "Old.Record.step", "Old.Record.step", "Old", kind="binder")
        cmd = {"kind": "declaration-command", "start": 0, "stop": len(text.rstrip())}
        plan = Migration({"rows": [{"module": "Old", "old": "Old.Record.step", "new": "Later.Record.step",
                                    "field_namespace": "Earlier.Record"}]})
        data = {"module": "Old", "source": text, "refs": [ref], "commands": [cmd]}
        result, issues = rewrite(data, plan)
        self.assertEqual(issues, [])
        self.assertIn(b"def _root_.Later.Record.step", result)
        self.assertIn(b"with_weak_namespace _root_.Earlier.Record export _root_.Later.Record (step)", result)
        self.assertIsNone(rewrite({**data, "commands": []}, plan)[0])

    def test_stale_capture_rejected(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Test.lean").write_text("def f := 2\n")
            capture = root / "index.json"
            capture.write_text(json.dumps({"schema_version": 1, "module": "Test", "source": "def f := 1\n"}))
            with self.assertRaisesRegex(ValueError, "exact source"):
                checked_capture(root, "Test.lean", capture)


class CollectionTests(unittest.TestCase):
    def test_collect_inherits_lake_setup_even_with_direct_lean(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.toml").write_text('name = "Fixture"\n')
            (root / "Fixture.lean").write_text("def value := 1\n")
            def run(args, **kwargs):
                self.assertEqual(kwargs["cwd"], root.resolve())
                if args[:3] == ["lake", "--no-build", "setup-file"]:
                    return subprocess.CompletedProcess(args, 0, json.dumps({"name": "Fixture", "options": {"maxSynthPendingDepth": 3}}), "")
                self.assertEqual(args[0], str((root / "lean").resolve()))
                self.assertEqual(json.loads(Path(args[-1]).read_text())["options"]["maxSynthPendingDepth"], 3)
                Path(args[-2]).write_text(json.dumps({"schema_version": 1, "module": "Fixture", "source": (root / "Fixture.lean").read_text(), "refs": [], "commands": []}))
                return subprocess.CompletedProcess(args, 0)
            with patch("klw1_namespace.subprocess.run", side_effect=run) as calls:
                collect(root, ["Fixture.lean"], root / "index", root / "lean")
            self.assertEqual(calls.call_count, 2)
            self.assertEqual(json.loads((root / "index/files.json").read_text()), ["Fixture.lean"])

    def test_one_collection_freezes_helper_across_all_files(self):
        with TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools = root / "tools"
            tools.mkdir()
            original = tools / "klw1_collect_refs.lean"
            original.write_bytes(b"tested helper version")
            for name in ("A", "B"):
                (root / (name + ".lean")).write_text("def value := 1\n")
            def run(args, **kwargs):
                self.assertNotEqual(Path(args[2]), original)
                self.assertEqual(Path(args[2]).read_bytes(), b"tested helper version")
                original.write_bytes(b"concurrent future release")
                Path(args[5]).write_text(json.dumps({"schema_version": 1, "module": args[3], "source": (root / args[4]).read_text(), "refs": [], "commands": []}))
                return subprocess.CompletedProcess(args, 0)
            with patch("klw1_namespace.HERE", tools), patch("klw1_namespace.subprocess.run", side_effect=run):
                collect(root, ["A.lean", "B.lean"], root / "index", root / "lean")
            fingerprints = {json.loads((root / "index" / (name + ".json")).read_text())["elaboration"]["collector_sha256"] for name in ("A", "B")}
            self.assertEqual(len(fingerprints), 1)

    def test_setup_failure_does_not_fall_back_to_empty_options(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.toml").touch()
            with patch("klw1_namespace.subprocess.run", return_value=subprocess.CompletedProcess([], 1, "", "missing dependency")) as calls, redirect_stderr(StringIO()):
                with self.assertRaisesRegex(ValueError, "build dependencies before collect"):
                    collect(root, ["Fixture.lean"], root / "index", root / "lean")
            self.assertEqual(calls.call_count, 1)
            self.assertFalse((root / "index/files.json").exists())


class LayerTests(unittest.TestCase):
    def setUp(self):
        k = "SerrePositivity.InfinityCategories.Kerodon"
        self.a, self.b, self.c = (f"{k}.{part}.Basic" for part in ("Early", "Later", "Comp"))
        self.i = "SerrePositivity.KST.Internal"
        self.graph = {self.a: {self.b, "Mathlib.X"}, self.b: set(), self.c: {self.i}, self.i: set()}
        self.config = {"schema_version": 1,
                       "modules": {self.a: "Portable", self.b: "SharedFoundation", self.c: "Comparison"},
                       "external_prefixes": ["Mathlib"],
                       "implementation_prefixes": ["SerrePositivity.KST"],
                       "sections": {f"{k}.Early": [1, 1], f"{k}.Later": [2, 1], f"{k}.Comp": [3, 1]},
                       "reverse_edges": [{"from": self.a, "to": self.b, "reason": "shared comparison"}],
                       "implementation_edges": [{"from": self.c, "to": self.i, "reason": "model input"}]}

    def test_same_section_rank_is_not_directory_rank(self):
        report = check(self.graph, self.config)
        self.assertFalse(report["violations"])
        self.assertEqual(len(report["approved_reverse_edges"]), 1)
        self.assertLess(report["topological_order"].index(self.b), report["topological_order"].index(self.a))

    def test_transitive_implementation_and_unresolved_import(self):
        self.graph[self.b] = {self.c, "SerrePositivity.Missing"}
        issues = check(self.graph, self.config)["violations"]
        self.assertIn({"kind": "portable-implementation-closure", "path": (self.a, self.b, self.c, self.i)}, issues)
        self.assertIn({"kind": "unresolved-import", "path": (self.b, "SerrePositivity.Missing")}, issues)

    def test_cycle_and_stale_exception(self):
        self.graph[self.b] = {self.a}
        self.assertIn("import-cycle", {r["kind"] for r in check(self.graph, self.config)["violations"]})
        self.graph[self.c].clear()
        with self.assertRaisesRegex(ValueError, "stale exception"):
            check(self.graph, self.config)


class ReviewTests(unittest.TestCase):
    def test_review_changes_section_and_preserves_holds_and_model_flags(self):
        path = "SerrePositivity/InfinityCategories/X.lean"
        outside = "SerrePositivity/KST/Y.lean"
        def row(p, scope, action):
            return {"source": p, "scope": scope, "action": action, "basis": "items", "section": "1.1",
                    "section_tag": "AAAA", "proposed_path": f"Old/{Path(p).name}", "evidence": "declaration",
                    "declarations": "old", "declaration_items": "1.1.1.1", "other_declarations": "",
                    "docstring_refs": "", "other_sections": "", "model_category": "verify-instance:X"}
        items = [{"number": "1.1.1.1", "status": "own", "declarations": f"X @ {path}:10"},
                 {"number": "2.2.1.1", "status": "none", "declarations": ""}]
        reviews = {"1.1.1.1": {"status_new": "none", "verdict": "unsure", "declarations_new": ""},
                   "2.2.1.1": {"status_new": "own", "verdict": "fix", "declarations_new": f"X @ {path}:10 | Y @ {outside}:12"}}
        sections = toc_sections("- Chapter 2 [0002] Tests\n  - 2.2 [BBBB] Other Stuff\n")
        refreshed, changes = refresh([row(path, "inside", "move"), row(outside, "external-candidate", "hold-K-theory")],
                                     items, reviews, sections, [outside])
        self.assertEqual(refreshed[0]["proposed_path"], "SerrePositivity/InfinityCategories/Kerodon/Tests/OtherStuff/X.lean")
        self.assertEqual(refreshed[0]["basis"], "review")
        self.assertEqual(refreshed[0]["model_category"], "verify-instance:X")
        self.assertEqual(refreshed[1]["move_approved"], "no")
        self.assertIn("unsure items", changes[0]["reason"])

    def test_stage_1_6_filters_evidence_and_retains_prior_partial_placements(self):
        paths = {n: f"SerrePositivity/InfinityCategories/{n}.lean"
                 for n in ("Partial", "Withdrawn", "Mathlib", "NewPartial", "NewNone")}

        def assignment(name, evidence):
            return {"source": paths[name], "scope": "inside", "action": "move",
                    "basis": "items", "section": "1.1", "section_tag": "AAAA",
                    "proposed_path": f"Old/{name}.lean", "evidence": evidence,
                    "declarations": name, "declaration_items": "1.1.1.1",
                    "other_declarations": "", "docstring_refs": "", "other_sections": ""}

        items, reviews = [], {}
        for i, (name, status) in enumerate(
            (("Partial", "own"), ("Withdrawn", "partial"), ("Mathlib", "mathlib"),
             ("NewPartial", "partial"), ("NewNone", "none")), 1
        ):
            number = f"2.2.1.{i}"
            items.append({"number": number, "status": "none", "declarations": ""})
            reviews[number] = {"status_new": status, "verdict": "fix",
                               "declarations_new": f"{name} @ {paths[name]}:10"}
        prior = [assignment("Partial", "partial+topic"), assignment("Withdrawn", "declaration")]
        sections = toc_sections("- Chapter 2 [0002] Tests\n  - 2.2 [BBBB] Other Stuff\n")
        refreshed, changes = refresh(prior, items, reviews, sections)
        retained, withdrawn = refreshed
        self.assertEqual(retained["proposed_path"], prior[0]["proposed_path"])
        self.assertEqual(retained["partial_placement_retained"], "yes")
        self.assertEqual(withdrawn["proposed_path"], prior[1]["proposed_path"])
        self.assertEqual(withdrawn["evidence"], "review-no-correspondence")
        self.assertEqual({r["source"] for r in changes if r["reason"] == "new source; assign manually"},
                         {paths["Mathlib"]})

    def test_cross_gate_and_missing_chapter(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            items = [{"number": "2.1.1.1"}]
            self.assertEqual(load_reviews(items, root, complete=False), {})
            with self.assertRaises(FileNotFoundError):
                load_reviews(items, root)
            with self.assertRaisesRegex(ValueError, "accept-cross-review"):
                check_review_gate({}, root, False)
            with self.assertRaisesRegex(ValueError, "cross report for Ch 4"):
                check_review_gate({}, root, True)


@unittest.skipUnless(os.getenv("KLW1_TEST_LEAN"), "set KLW1_TEST_LEAN and use the build lock")
class LeanIntegrationTests(unittest.TestCase):
    def test_qualified_relative_and_open_rewrite_then_elaborate(self):
        lean = os.environ["KLW1_TEST_LEAN"]
        helper = Path(__file__).with_name("klw1_collect_refs.lean").resolve()
        text = """-- 日本語と Old.f
namespace Old
def f (x : Nat) := x + 1
structure Box where
  value : Nat
def destruct (b : Box) : Nat := by
  cases b with
  | mk value => exact value
def destructExplicit (b : Box) : Nat := by
  cases b with
  | @mk value => exact value
def rebuild (b : Box) : Box where
  value := b.value
def updateBox (b : Box) : Box := { b with value := 4 }
namespace Nested
def result := f 0
end Nested
inductive Branch where
  | bead : Branch
  | join : Branch → Branch → Branch
def collapseBranch (b : Branch) : Nat := by
  cases b with
  | bead => exact 0
  | join left right => exact 1
scoped notation "kRef" => f 1
end Old

open Old
open Old (f)
open Old renaming f -> ofn
open scoped Old
def rel := f 3
def rel2 := ofn 3
def fully := Old.f 3
def explicit := @Old.f 5
def shadow (f : Nat) := f + 1
def dot (x : Old.Box) := x.value
def localOpen := open Old in f 4
def withNotation := kRef
"""
        with TemporaryDirectory() as directory:
            root = Path(directory)
            path = "formalization-plans/drafts/Old.lean"
            source, capture, after = (root / n for n in (path, "refs.json", "After.lean"))
            source.parent.mkdir(parents=True)
            source.write_text(text)
            owner = module_name(path)
            subprocess.run([lean, "--run", str(helper), owner, path, capture.name], cwd=root, check=True)
            data = checked_capture(root, path, capture)
            symbols = ["Old.f", "Old.Box", "Old.Box.mk", "Old.Box.value", "Old.destruct", "Old.destructExplicit", "Old.rebuild", "Old.updateBox", "Old.Nested.result", "Old.Branch", "Old.Branch.bead", "Old.Branch.join", "Old.collapseBranch"]
            plan = Migration({"rows": [{"module": owner, "old": n, "new": n.replace("Old.", "New.Home.", 1)} for n in symbols],
                              "namespaces": {owner: {"Old": "New.Home"}}, "opens": {"Old": "New.Home"}})
            result, issues = rewrite(data, plan)
            self.assertEqual(issues, [])
            self.assertIn(b"namespace New.Home", result)
            self.assertIn(b"open _root_.New.Home renaming f -> ofn", result)
            self.assertIn(b"x.value", result)
            self.assertIn(b"value := ", result)
            self.assertIn(b"@_root_.New.Home.f", result)
            self.assertIn(b"def shadow (f : Nat) := f + 1", result)
            after.write_bytes(result + b"\nexample : fully = 4 := rfl\nexample : withNotation = 2 := rfl\n")
            subprocess.run([lean, after.name], cwd=root, check=True)

    def test_configured_options_and_explicit_universes(self):
        lean = os.environ["KLW1_TEST_LEAN"]
        helper = Path(__file__).with_name("klw1_collect_refs.lean").resolve()
        with TemporaryDirectory() as directory:
            root = Path(directory)
            text = """import Lean
open Lean in
run_cmd do
  let opts ← getOptions
  unless opts.get `maxSynthPendingDepth (1 : Nat) == 3 do throwError "lost depth"
  unless opts.get `relaxedAutoImplicit true == false do throwError "lost implicit policy"
  unless Elab.async.get opts == false do throwError "collector must be synchronous"
universe u
namespace Old
def value (α : Type u) : Type u := α
end Old
-- 日本語：宇宙の構文はそのまま保持する。
#check Old.value.{u}
#check Old.value.{max u 1}
"""
            (root / "Fixture.lean").write_text(text)
            setup = {"name": "Fixture", "package": "Fixture", "isModule": False, "plugins": [], "dynlibs": [], "importArts": {}, "options": {"maxSynthPendingDepth": 3, "relaxedAutoImplicit": False, "Elab.async": True}}
            (root / "setup.json").write_text(json.dumps(setup))
            subprocess.run([lean, "--run", str(helper), "Fixture", "Fixture.lean", "refs.json", "setup.json"], cwd=root, check=True)
            data = checked_capture(root, "Fixture.lean", root / "refs.json")
            self.assertEqual(data["elaboration"]["setup_options"]["maxSynthPendingDepth"], 3)
            refs = [r for r in data["refs"] if r["kind"] == "term" and r["name"] == "Old.value"]
            self.assertEqual(len({(r["start"], r["stop"]) for r in refs}), 2)
            self.assertTrue(all(text.encode()[r["start"]:r["stop"]] == b"Old.value" for r in refs))
            plan = Migration({"rows": [{"module": "Fixture", "old": "Old.value", "new": "New.value"}], "namespaces": {"Fixture": {"Old": "New"}}})
            rendered, issues = rewrite(data, plan)
            self.assertEqual(issues, [])
            self.assertIn(b"_root_.New.value.{u}", rendered)
            self.assertIn(b"_root_.New.value.{max u 1}", rendered)
            (root / "setup.json").write_text(json.dumps(setup | {"name": "Wrong"}))
            result = subprocess.run([lean, "--run", str(helper), "Fixture", "Fixture.lean", "bad.json", "setup.json"], cwd=root, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("setup module mismatch", result.stderr)
            self.assertFalse((root / "bad.json").exists())

    def test_keep_partial_namespace_when_destination_module_has_another_name(self):
        lean = os.environ["KLW1_TEST_LEAN"]
        helper = Path(__file__).with_name("klw1_collect_refs.lean").resolve()
        with TemporaryDirectory() as directory:
            root = Path(directory)
            env = dict(os.environ, LEAN_PATH=directory + os.pathsep + os.environ.get("LEAN_PATH", ""))
            (root / "Base.lean").write_text("namespace Shared\ndef retained : Nat := 2\nend Shared\n")
            (root / "Original.lean").write_text("import Base\nnamespace Shared\ndef moved : Nat := 1\nend Shared\nnamespace Removed\ndef extra : Nat := 4\nend Removed\n")
            for name in ("Base", "Original"):
                subprocess.run([lean, "-o", name + ".olean", name + ".lean"], cwd=root, env=env, check=True)
            text = "import Original\nopen Shared Removed\ndef result := moved + retained + extra\nexample : result = 7 := rfl\n"
            (root / "Uses.lean").write_text(text)
            subprocess.run([lean, "--run", str(helper), "Uses", "Uses.lean", "refs.json"], cwd=root, env=env, check=True)
            data = checked_capture(root, "Uses.lean", root / "refs.json")
            plan = Migration({"modules": {"Original": "MovedLayout"}, "rows": [{"module": "Original", "old": "Shared.moved", "new": "New.Actual.moved"}, {"module": "Original", "old": "Removed.extra", "new": "New.Actual.extra"}], "namespaces": {"Original": {"Shared": "New.Actual"}}, "opens": {"Shared": "Shared", "Removed": "Removed"}, "module_opens": {"Uses": {"Removed": None}}})
            rendered, issues = rewrite(data, plan)
            self.assertEqual(issues, [])
            self.assertIn(b"open Shared", rendered)
            self.assertIn(b"_root_.New.Actual.moved + retained", rendered)
            self.assertNotIn(b"open _root_.MovedLayout", rendered)
            self.assertNotIn(b"open Shared Removed", rendered)
            self.assertIn(b"_root_.New.Actual.extra", rendered)
            (root / "MovedLayout.lean").write_text("import Base\nnamespace New.Actual\ndef moved : Nat := 1\ndef extra : Nat := 4\nend New.Actual\n")
            subprocess.run([lean, "-o", "MovedLayout.olean", "MovedLayout.lean"], cwd=root, env=env, check=True)
            (root / "After.lean").write_bytes(rendered)
            subprocess.run([lean, "After.lean"], cwd=root, env=env, check=True)

    def test_detached_method_resolves_in_importing_module(self):
        lean = os.environ["KLW1_TEST_LEAN"]
        helper = Path(__file__).with_name("klw1_collect_refs.lean").resolve()
        with TemporaryDirectory() as directory:
            root = Path(directory)
            original = root / "Original.lean"
            original.write_text("""module
@[expose] public section
namespace Old
structure Record where
  val : Nat
def Record.addOffset (n : Nat) (r : Record) := n + r.val
example (r : Record) : r.addOffset 2 = 2 + r.val := rfl
end Old
""")
            capture = root / "refs.json"
            subprocess.run([lean, "--run", str(helper), "Original", original.name, capture.name],
                           cwd=root, check=True)
            data = checked_capture(root, original.name, capture)
            plan = Migration({"rows": [
                {"old": "Old.Record", "new": "Early.Record", "module": "Original"},
                {"old": "Old.Record.val", "new": "Early.Record.val", "module": "Original"},
                {"old": "Old.Record.addOffset", "new": "Later.Record.addOffset", "module": "Original",
                 "field_namespace": "Early.Record"},
            ], "namespaces": {"Original": {"Old": "Early"}}})
            rendered, issues = rewrite(data, plan)
            self.assertEqual(issues, [])
            (root / "Moved.lean").write_bytes(rendered)
            subprocess.run([lean, "-o", "Moved.olean", "Moved.lean"], cwd=root, check=True)
            (root / "Uses.lean").write_text(
                "import Moved\nexample (r : Early.Record) : r.addOffset 2 = Later.Record.addOffset 2 r := rfl\n")
            subprocess.run([lean, "Uses.lean"], cwd=root, check=True,
                           env=dict(os.environ, LEAN_PATH=directory))

    @unittest.skipUnless(os.getenv("KLW1_TEST_ALIAS_HELPER"), "set KLW1_TEST_ALIAS_HELPER and LEAN_PATH")
    def test_generated_aliases_elaborate_with_f2_helper(self):
        lean = os.environ["KLW1_TEST_LEAN"]
        helper = os.environ["KLW1_TEST_ALIAS_HELPER"]
        plan = Migration({"rows": [
            {"old": "Old.g", "new": "New.g", "module": "Moved"},
            {"old": "Old.g_eq", "new": "New.g_eq", "module": "Moved"},
        ]})
        selected = {r["old"]: r for r in plan.symbols.values()}
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Moved.lean").write_text(
                "module\n@[expose] public section\ndef New.g (n : Nat) := n\n"
                "theorem New.g_eq (n : Nat) : New.g n = n := rfl\n")
            (root / "Aliases.lean").write_text(render_aliases(selected, plan, helper, "2026-11-07"))
            env = dict(os.environ, LEAN_PATH=directory + os.pathsep + os.environ["LEAN_PATH"])
            for module in ("Moved", "Aliases"):
                subprocess.run([lean, "-o", module + ".olean", module + ".lean"], cwd=root, env=env, check=True)
            (root / "Consumer.lean").write_text("import Aliases\nexample (n : Nat) : Old.g n = n := Old.g_eq n\n")
            subprocess.run([lean, "Consumer.lean"], cwd=root, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
