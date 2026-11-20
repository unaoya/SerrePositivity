#!/usr/bin/env python3
"""Run the table and Lean-format upgrade fixtures under a bulk build slot."""
import argparse
import json
from pathlib import Path
import sqlite3
import subprocess
import tempfile

from audit import ROOT, Run, SCHEMA, artifact_path, compile_worker, write_json
from rules import World, check

WITNESS = """module
public import Lean
public section
namespace Audit2Fixture
axiom witness : False
private theorem hidden : False := witness
theorem throughPrivate : False := hidden
inductive Box where
  | make : (False ∧ True) → Box
class Mark where
  point : Nat
instance marker : Mark := ⟨0⟩
unsafe def fast (n : Nat) : Nat := n
@[implemented_by fast] def exampleRuntime (n : Nat) : Nat := n
@[extern "audit2_unused_fixture_hook"] opaque externalHook : Nat → Nat
partial def sequence (n : Nat) : Nat := sequence (n + 1)
opaque trustedValue : False := hidden
theorem directSorry : True := by sorry
theorem clean : True := True.intro
end Audit2Fixture
"""


def negative(run, label, args, cwd, diagnostic=None, expected_rc=None):
    log = run.out / (label + ".log")
    with log.open("w") as out:
        status = subprocess.run(args, cwd=cwd, stdout=out, stderr=subprocess.STDOUT).returncode
    if (status == 0 or (expected_rc is not None and status != expected_rc) or
            (diagnostic is not None and diagnostic not in log.read_text(errors="replace"))):
        raise RuntimeError(f"{label}: expected {diagnostic!r}, got {status}; see {log}")


def table_rules():
    db = sqlite3.connect(":memory:")
    db.row_factory = sqlite3.Row
    db.executescript(SCHEMA)
    db.executemany("INSERT INTO module VALUES (?,?,?,?)",
                   [("F", "fixture", '["F.Blocked"]', 2), ("F.Blocked", "fixture", "[]", 0)])
    def row(name, typ, value, axioms, public, kind):
        return ("F", name, kind, public, 0, 0, "00", "01", json.dumps(typ),
                json.dumps(value), "[]", None, "[]", 0, None, 0, 0, None,
                json.dumps(axioms), "fixture")
    db.executemany("INSERT INTO decl VALUES (" + ",".join(["?"] * 20) + ")", [
        row("good", [], ["ForbiddenType"], [], 1, "thm"),
        row("bad", ["ForbiddenType"], ["sorryAx", "old"], ["sorryAx"], 0, "axiom"),
    ])
    world = World(db)
    good = [["F", "good"]]
    bad = [["F", "bad"]]
    cases = [
        ("strict-sorry", dict(declarations=good), dict(declarations=bad)),
        ("direct-edge", dict(edge="type", forbidden=["ForbiddenType"], declarations=good),
         dict(edge="type", forbidden=["ForbiddenType"], declarations=bad)),
        ("direct-edge", dict(edge="value", forbidden=["old"], declarations=good),
         dict(edge="value", forbidden=["old"], declarations=bad)),
        ("shape", dict(declarations=good, expect=dict(public=1, kind="thm", module="F")),
         dict(declarations=bad, expect=dict(public=1, kind="thm", module="F"))),
        ("forbidden-kind", dict(declarations=good, forbidden=["axiom"]),
         dict(declarations=bad, forbidden=["axiom"])),
        ("reachable", dict(starts=["good"], forbidden=["old"]),
         dict(starts=["bad"], forbidden=["old"])),
        ("direct-sorry-files", dict(declarations=bad, allowed=["F.lean"]),
         dict(declarations=bad, allowed=[])),
        ("visited-modules", dict(expected=["F"], actual=["F"]),
         dict(expected=["F"], actual=[])),
        ("import-components", dict(roots=["F.Blocked"], prefix="F", forbidden=["Missing"]),
         dict(roots=["F"], prefix="F", forbidden=["Blocked"])),
    ]
    for kind, positive, negative_rule in cases:
        assert not check(world, dict(kind=kind, **positive)), (kind, positive)
        assert check(world, dict(kind=kind, **negative_rule)), (kind, negative_rule)
    db.execute("UPDATE decl SET axioms=NULL WHERE name='good'")
    assert check(world, dict(kind="strict-sorry", declarations=good))
    return len(cases) + 1


def format_test(run, workers):
    with tempfile.TemporaryDirectory(prefix="audit2-fixture-") as tmp:
        project = Path(tmp)
        (project / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
        (project / "lakefile.toml").write_text('name = "Audit2Fixture"\n[[lean_lib]]\nname = "Witness"\n')
        source = project / "Witness.lean"
        source.write_text(WITNESS)
        (run.out / "Witness.lean").write_text(WITNESS)
        lake = ["lake", "--dir", project]
        run.execute("fixture-build", [*lake, "build", "+Witness"])
        module = run.lines("fixture-modules", ["Witness"])
        check_build = [*lake, "env", workers["Build"], module, "--dir", project, "--no-build", "--rehash", "--no-cache"]
        run.execute("fixture-fresh", check_build)
        compiled = project / ".lake/build/lib/lean/Witness.olean"
        inp = run.lines("fixture-artifacts", [f"Witness\t{compiled}"])
        direct = run.out / "fixture-direct.jsonl"
        run.execute("fixture-direct", [workers["Artifacts"], "extract", inp, direct])
        slow = run.out / "fixture-slow.jsonl"
        run.execute("fixture-oracle", [*lake, "env", workers["Oracle"], module, module, slow, "all"])
        direct_rows = {r[0]: r for line in direct.open() if len(r := json.loads(line)) == 16}
        slow_rows = {r[1]: set(r[2]) for line in slow.open() if len(r := json.loads(line)) == 4}
        assert direct_rows.keys() == slow_rows.keys()
        assert all(set(r[10]) == slow_rows[n] for n, r in direct_rows.items() if r[10] is not None)
        missing = [n for n, r in direct_rows.items() if r[10] is None]
        assert missing
        requested = run.lines("fixture-missing", (f"Witness\t{n}" for n in missing))
        fallback = run.out / "fixture-fallback.jsonl"
        run.execute("fixture-fallback", [*lake, "env", workers["Oracle"], module, requested, fallback, "missing"])
        fallback_rows = {r[1]: set(r[2]) for l in fallback.open() if len(r := json.loads(l)) == 4}
        assert fallback_rows == {n: slow_rows[n] for n in missing}
        space = "Audit2Fixture."
        assert slow_rows[space + "throughPrivate"] == {space + "witness"}
        assert slow_rows[space + "trustedValue"] == {space + "witness"}
        assert slow_rows[space + "directSorry"] == {"sorryAx"}
        assert not slow_rows[space + "clean"]
        assert direct_rows[space + "clean"][10] == []
        assert direct_rows[space + "throughPrivate"][10] == [space + "witness"]
        assert any(r[3] and r[10] is None for r in direct_rows.values())
        assert direct_rows[space + "trustedValue"][1] == "opaque"
        assert direct_rows[space + "trustedValue"][6] is not None
        assert direct_rows[space + "Box"][9] == [space + "Box.make"]
        assert direct_rows[space + "marker"][11]
        assert direct_rows[space + "fast"][12]
        assert direct_rows[space + "exampleRuntime"][13] == space + "fast"
        assert direct_rows[space + "externalHook"][14]
        duplicates = project / "Witness"
        duplicates.mkdir()
        prep = "module\npublic import Witness\npublic section\nnamespace Audit2Fixture\n"
        (duplicates / "Left.lean").write_text(prep + "theorem repeated : True := True.intro\nend Audit2Fixture\n")
        (duplicates / "Right.lean").write_text(prep + "theorem repeated : True := False.elim witness\nend Audit2Fixture\n")
        names = ["Witness.Left", "Witness.Right"]
        run.execute("fixture-duplicate-build", [*lake, "build", *("+" + n for n in names)])
        duplicate_roots = run.lines("fixture-duplicate-modules", names)
        duplicate_out = run.out / "fixture-duplicate.jsonl"
        run.execute("fixture-duplicate-oracle", [*lake, "env", workers["Oracle"], duplicate_roots,
                                                  duplicate_roots, duplicate_out, "all"])
        by_owner = {r[0]: (set(r[2]), r[3]) for l in duplicate_out.open() if len(r := json.loads(l)) == 4
                    and r[1] == space + "repeated"}
        assert by_owner == {"Witness.Left": (set(), "import"),
                            "Witness.Right": ({space + "witness"}, "owner-record")}, by_owner
        source.write_text(WITNESS + "\ntheorem changedAfterBuild : True := True.intro\n")
        negative(run, "fixture-stale-source", check_build, project, expected_rc=3)
        wrong = run.lines("fixture-wrong-hash", [f"{compiled}\t0000000000000000"])
        negative(run, "fixture-wrong-artifact", [workers["Artifacts"], "hashes", wrong],
                 project, "artifact hash mismatch")
        return {"declarations": len(direct_rows), "fallback": len(missing),
                "rules": table_rules(), "shadowed_record_checked": True, "stale_source_rejected": True, "wrong_artifact_rejected": True}


def mathlib_context_test(run, workers):
    # This small project module imports Mathlib's cross-reference attribute
    # and produces private hygienic names. Check both paths against the
    # currently installed dependency and the current local Lake trace.
    owner = "SerrePositivity.Util.Citation"
    targets = run.lines("mathlib-modules", [owner])
    run.execute("mathlib-fresh", ["lake", "env", workers["Build"], targets,
                                 "--no-build", "--rehash", "--no-cache"])
    inputs = run.lines("mathlib-artifacts", [f"{owner}\t{artifact_path(owner)}"])
    direct = run.out / "mathlib-direct.jsonl"
    run.execute("mathlib-direct", [workers["Artifacts"], "extract", inputs, direct])
    rows = {row[0]: row for line in direct.open() if len(row := json.loads(line)) == 16}
    wants = run.lines("mathlib-private", (f"{owner}\t{n}" for n,r in rows.items() if r[10] is None))
    slow = run.out / "mathlib-slow.jsonl"
    missing = run.out / "mathlib-fallback.jsonl"
    for mode, wanted, output in (("all", targets, slow), ("missing", wants, missing)):
        run.execute("mathlib-oracle-" + mode, ["lake", "env", workers["Oracle"], targets,
                                              wanted, output, mode])
    all_ax = {r[1]: set(r[2]) for l in slow.open() if len(r := json.loads(l)) == 4}
    back = {r[1]: set(r[2]) for l in missing.open() if len(r := json.loads(l)) == 4}
    assert rows.keys() == all_ax.keys()
    assert any("._hygCtx." in n for n in back)
    assert back == {n:all_ax[n] for n,r in rows.items() if r[10] is None}
    assert all(set(r[10]) == all_ax[n] for n,r in rows.items() if r[10] is not None)
    return {"declarations":len(rows), "fallback":len(back)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("out")
    parser.add_argument("--workers", type=Path, help="directory with the three current native workers")
    args = parser.parse_args()
    run = Run(args.out)
    names = ("Artifacts", "Oracle", "Build")
    workers = {n: args.workers.resolve() / n if args.workers else compile_worker(run, n) for n in names}
    result = format_test(run, workers)
    result["mathlib_context"] = mathlib_context_test(run, workers)
    write_json(run.out / "selftest.json", result)
    print(json.dumps(result, ensure_ascii=False))


if __name__ == "__main__":
    main()
