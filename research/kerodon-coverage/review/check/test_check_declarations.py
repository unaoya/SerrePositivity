"""出力欠落・未知名・異常公理を誤って正常判定しないことの回帰検査。"""
import json
import unittest
from collections import Counter
from pathlib import Path

from check_declarations import axiom_names, lean_input, parse_output, reference


def message(line, text, severity="information"):
    return json.dumps({"severity": severity, "data": text,
                       "pos": {"line": line, "column": 0}, "endPos": None})


class AuditTests(unittest.TestCase):
    def setUp(self):
        self.commands = {"a": {"check_line": 7, "axioms_line": 8},
                         "b": {"check_line": 11, "axioms_line": 12}}

    def parse(self, lines, code=0, stderr=""):
        return parse_output("\n".join(lines), stderr, code, self.commands)

    def valid(self):
        return [message(7, "Nat.add : Nat → Nat → Nat"),
                message(8, "'Nat.add' does not depend on any axioms"),
                message(11, "Example.foo :\n  ∀ (α : Type), α = α"),
                message(12, "'Example.foo' depends on axioms: [propext,\n Classical.choice, Quot.sound]")]

    def test_standard_and_multiline(self):
        result = self.parse(self.valid())
        self.assertEqual([r["state"] for r in result.values()], ["found", "found"])
        self.assertEqual(result["a"]["axioms"], [])
        self.assertEqual(result["b"]["extra_axioms"], [])
        self.assertIn("∀", result["b"]["type"])

    def test_sorry_and_other_axioms(self):
        lines = self.valid()
        lines[-1] = message(12, "'Example.foo' depends on axioms: [sorryAx, Example.assumption, propext]")
        result = self.parse(lines)["b"]
        self.assertEqual(result["state"], "found")
        self.assertEqual(result["extra_axioms"], ["Example.assumption", "sorryAx"])

    def test_axiom_universe_arguments_from_real_lean_output(self):
        self.assertEqual(axiom_names("'SSet' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]"),
                         ["propext", "Classical.choice", "Quot.sound"])
        self.assertEqual(axiom_names("'Test' depends on axioms: [Example.ax.{u, v}, sorryAx.{u}]"),
                         ["Example.ax", "sorryAx"])

    def test_unknown_does_not_hide_other_success(self):
        lines = self.valid()[:2] + [message(11, "Unknown identifier `Missing`", "error"),
                                    message(12, "Unknown constant `Missing`", "error")]
        result = self.parse(lines, code=1)
        self.assertEqual(result["a"]["state"], "found")
        self.assertEqual(result["b"]["state"], "not_found")

    def test_inference_error_is_not_missing(self):
        result = self.parse(self.valid()[:2] + [message(11, "failed to synthesize\n ModelCategory SSet", "error")], code=1)
        self.assertEqual(result["b"]["state"], "check_failed")

    def test_import_error_invalidates_all(self):
        result = self.parse(self.valid() + [message(1, "object file does not exist", "error")], code=1)
        self.assertTrue(all(r["state"] == "output_invalid" for r in result.values()))

    def test_no_output_is_not_success(self):
        self.assertEqual(self.parse([])["a"]["state"], "check_failed")
        self.assertEqual(self.parse([], code=1)["a"]["state"], "output_invalid")
        self.assertEqual(self.parse(self.valid(), code=-9)["a"]["state"], "output_invalid")

    def test_malformed_json_and_stderr(self):
        self.assertEqual(self.parse(self.valid() + ["unexpected text"])["a"]["state"], "output_invalid")
        self.assertEqual(self.parse(self.valid() + ['{"pos": null}'])["a"]["state"], "output_invalid")
        self.assertEqual(self.parse(self.valid(), stderr="uncaught exception")["a"]["state"], "output_invalid")

    def test_axioms_output_required(self):
        lines = self.valid()
        lines[-1] = message(12, "unrecognized axiom format")
        self.assertEqual(self.parse(lines)["b"]["state"], "axioms_unparsed")
        self.assertIsNone(axiom_names("unrecognized"))

    def test_reference_paths_and_unicode(self):
        ref = reference("SSet.Truncated.Quasicategory₂ @ .lake/packages/mathlib/Mathlib/Foo.lean:53")
        self.assertEqual(ref["preparation"], "ready")
        self.assertEqual(ref["module"], "Mathlib.Foo")
        self.assertEqual(ref["source_line"], "53")
        self.assertEqual(reference("Functor.const @ Mathlib/Foo.lean")["preparation"], "ready")

    def test_unresolved_not_silently_truncated(self):
        for raw in ["Foo / Bar @ Mathlib/Foo.lean:5", "instance Foo X @ Mathlib/Foo.lean:5",
                    "Foo (記法) @ Mathlib/Foo.lean:5", "Foo @ Mathlib/Foo.lean:5,7",
                    "Foo @ Mathlib/../Foo.lean:5", "Foo; #eval bad @ Mathlib/Foo.lean:5"]:
            with self.subTest(raw=raw):
                self.assertEqual(reference(raw)["preparation"], "unresolved_reference")

    def test_command_positions(self):
        ref = reference("Nat.add @ Mathlib/Foo.lean:5")
        text, commands = lean_input("Mathlib.Foo", [ref])
        lines = text.splitlines()
        self.assertEqual(lines[commands[ref["id"]]["check_line"] - 1], "#check @Nat.add")
        self.assertEqual(lines[commands[ref["id"]]["axioms_line"] - 1], "#print axioms Nat.add")

    def test_recorded_lean_435_output(self):
        fixtures = Path(__file__).parent / "fixtures/real-lean"
        modules = sorted(fixtures.glob("*/execution.json"))
        self.assertEqual(len(modules), 3)
        counts = Counter()
        for path in modules:
            metadata = json.loads(path.read_text())
            commands = json.loads(path.with_name("commands.json").read_text())
            result = parse_output(path.with_name("lean.stdout.jsonl").read_text(),
                                  path.with_name("lean.stderr.txt").read_text(),
                                  metadata["lean_returncode"], commands)
            counts.update(r["state"] for r in result.values())
            self.assertFalse(any(r["extra_axioms"] for r in result.values()))
        self.assertEqual(counts, Counter(found=8, not_found=10))


if __name__ == "__main__":
    unittest.main()
