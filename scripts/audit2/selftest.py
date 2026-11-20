#!/usr/bin/env python3
"""Run the table and Lean-format upgrade fixtures under a bulk build slot."""
import argparse
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import tempfile
import time
from unittest.mock import patch

import audit
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


def shared_artifact_test(run, workers, project, source, compiled, inputs):
    sibling = project.with_name("sibling")
    git = ["git", "-C", project, "-c", "core.hooksPath=/dev/null",
           "-c", "user.name=Audit Fixture", "-c", "user.email=audit@example.invalid"]
    for args in (["init", "--quiet"], ["add", "lean-toolchain", "lakefile.toml", source.name],
                 ["commit", "--quiet", "-m", "Shared artifact fixture"],
                 ["worktree", "add", "--quiet", "--detach", sibling]):
        subprocess.run([*git, *args], check=True)

    other_output = sibling / compiled.relative_to(project)
    other_output.parent.mkdir(parents=True)
    other_output.hardlink_to(compiled)
    original_stat = compiled.stat()
    assert compiled.samefile(other_output)
    original = audit.file_stamp(compiled)
    (sibling / source.name).write_text(WITNESS + "\ndef siblingBuild : Nat := 17\n")
    ready, release = sibling / "build-ready", sibling / "build-release"
    (sibling / "Witness").mkdir()
    (sibling / "Witness/Gate.lean").write_text(f"""module
public import Witness

#eval do
  IO.FS.writeFile {json.dumps(str(ready))} ""
  let release : System.FilePath := {json.dumps(str(release))}
  for _ in [0:6000] do
    if ← release.pathExists then return ()
    IO.sleep 10
  throw <| IO.userError "shared-artifact fixture timed out waiting for audit"
""")
    sources = {"Witness": source}
    with patch.multiple(audit, ROOT=project, LIB=compiled.parent), \
         patch.object(audit, "compile_worker", return_value=workers["Build"]):
        _, stamps = audit.preflight(run, sources, sources, workers["Artifacts"])
        log = run.out / "fixture-sibling-build.log"
        with log.open("w") as output, subprocess.Popen(
            ["lake", "build", "--no-cache", "--rehash", "+Witness.Gate"], cwd=sibling,
            stdout=output, stderr=subprocess.STDOUT,
        ) as builder:
            try:
                deadline = time.monotonic() + 45
                while not ready.exists() and builder.poll() is None and time.monotonic() < deadline:
                    time.sleep(0.02)
                assert ready.exists() and builder.poll() is None, f"sibling build did not reach gate: {log}"
                now = compiled.stat()
                assert now.st_ino == original_stat.st_ino and now.st_nlink == original_stat.st_nlink - 1
                assert now.st_ctime_ns != original_stat.st_ctime_ns and not compiled.samefile(other_output)
                assert audit.file_stamp(other_output) != original
                run.execute("fixture-shared-extract", [workers["Artifacts"], "extract", inputs,
                                                        run.out / "fixture-shared-extract.jsonl"])
                audit.assert_stamps(stamps)
                assert audit.file_stamp(compiled) == original
                assert builder.poll() is None, f"sibling build ended before audit finished: {log}"
            finally:
                release.touch()
            assert builder.wait() == 0, f"sibling build failed: {log}"

    # Edit a byte without changing size, inode, or mtime. Check every type of
    # input that must still be rejected by the audit's final content check.
    for path in (source, compiled.with_suffix(".trace"), compiled):
        data = path.read_bytes()
        # Lake may publish read-only or cached outputs. Mutate a private copy
        # at the audited path so the fixture cannot change a shared cache.
        copy = path.with_name(path.name + ".fixture-copy")
        copy.write_bytes(data)
        copy.replace(path)
        old = path.stat()
        try:
            path.write_bytes(data[:-1] + bytes([data[-1] ^ 1]))
            os.utime(path, ns=(old.st_atime_ns, old.st_mtime_ns))
            now = path.stat()
            assert (now.st_ino, now.st_size, now.st_mtime_ns) == (old.st_ino, old.st_size, old.st_mtime_ns)
            try:
                audit.assert_stamps(stamps)
            except audit.Failure as error:
                assert str(error) == f"preflight input changed during audit: {path}"
            else:
                raise AssertionError(f"audit accepted changed bytes in {path}")
        finally:
            path.write_bytes(data)
    audit.assert_stamps(stamps)
    return {"sibling_build_overlapped": True, "ctime_changed": True,
            "changed_source_trace_and_artifact_rejected": True}


def format_test(run, workers):
    with tempfile.TemporaryDirectory(prefix="audit2-fixture-") as tmp:
        project = Path(tmp) / "record"
        project.mkdir()
        (project / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
        (project / "lakefile.toml").write_text('name = "Audit2Fixture"\n[[lean_lib]]\nname = "Witness"\n')
        source = project / "Witness.lean"
        source.write_text(WITNESS)
        (run.out / "Witness.lean").write_text(WITNESS)
        lake = ["lake", "--dir", project]
        run.execute("fixture-build", [*lake, "build", "--no-cache", "+Witness"])
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
        run.execute("fixture-duplicate-build", [*lake, "build", "--no-cache", *("+" + n for n in names)])
        duplicate_roots = run.lines("fixture-duplicate-modules", names)
        duplicate_out = run.out / "fixture-duplicate.jsonl"
        run.execute("fixture-duplicate-oracle", [*lake, "env", workers["Oracle"], duplicate_roots,
                                                  duplicate_roots, duplicate_out, "all"])
        by_owner = {r[0]: (set(r[2]), r[3]) for l in duplicate_out.open() if len(r := json.loads(l)) == 4
                    and r[1] == space + "repeated"}
        assert by_owner == {"Witness.Left": (set(), "import"),
                            "Witness.Right": ({space + "witness"}, "owner-record")}, by_owner
        shared = shared_artifact_test(run, workers, project, source, compiled, inp)
        source.write_text(WITNESS + "\ntheorem changedAfterBuild : True := True.intro\n")
        negative(run, "fixture-stale-source", check_build, project, expected_rc=3)
        wrong = run.lines("fixture-wrong-hash", [f"{compiled}\t0000000000000000"])
        negative(run, "fixture-wrong-artifact", [workers["Artifacts"], "hashes", wrong],
                 project, "artifact hash mismatch")
        return {"declarations": len(direct_rows), "fallback": len(missing),
                "rules": table_rules(), "shadowed_record_checked": True, "stale_source_rejected": True,
                "wrong_artifact_rejected": True, "shared_artifact": shared}


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
