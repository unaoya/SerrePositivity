#!/usr/bin/env python3
"""Build and audit independent Git worktrees to test the merge gate."""
import argparse
import csv
import json
from pathlib import Path
import shutil
import subprocess
import sys

from audit import ROOT, write_json
from coverage import sha


SOURCE = """module
public import Lean

public section

namespace Fixture
theorem kanQuillen_model_exists : True := by sorry
def bound : Nat := 0
theorem named : bound ≤ 10 := by decide
end Fixture

namespace SerrePositivity
theorem main_statement : True := True.intro
end SerrePositivity
"""


def test(out, declaration_diff=False):
    project = out / "base"
    project.mkdir(parents=True)
    commands = out / "commands.log"

    def run(cwd, *args, expected=0):
        with commands.open("a") as log:
            print(f"{cwd.name}: {args}", file=log, flush=True)
            p = subprocess.run(args, cwd=cwd, stdout=log, stderr=subprocess.STDOUT)
        if p.returncode != expected:
            raise RuntimeError(f"expected exit {expected}, got {p.returncode}: {args}; see {commands}")

    def git(cwd, *args):
        run(cwd, "git", "-c", "core.hooksPath=/dev/null", "-c", "user.name=Audit Fixture",
            "-c", "user.email=audit@example.invalid", *args)

    dependency = out / "mathlib-package"
    dependency.mkdir()
    (dependency / "lakefile.toml").write_text('name = "mathlib"\n')
    git(dependency, "init", "-q")
    git(dependency, "add", "lakefile.toml")
    git(dependency, "commit", "-qm", "Pin empty fixture dependency")
    pin = subprocess.check_output(["git", "-C", dependency, "rev-parse", "HEAD"], text=True).strip()

    shutil.copyfile(ROOT / "lean-toolchain", project / "lean-toolchain")
    (project / "lakefile.toml").write_text(
        'name = "Fixture"\ndefaultTargets = ["SerrePositivity"]\n\n'
        '[[lean_lib]]\nname = "SerrePositivity"\n\n'
        '[[require]]\nname = "mathlib"\npath = "../mathlib-package"\n')
    run(project, "lake", "update")
    manifest = project / "lake-manifest.json"
    data = json.loads(manifest.read_text())
    data["packages"][0]["rev"] = pin
    write_json(manifest, data)
    (project / ".gitignore").write_text(".lake/\n__pycache__/\n")
    source = SOURCE
    if declaration_diff:
        source = source.replace("end Fixture", """class Available where
  value : Nat
def availableSeed : Available := ⟨0⟩
end Fixture""")
    (project / "SerrePositivity.lean").write_text(source)
    shutil.copytree(ROOT / "scripts/audit2", project / "scripts/audit2",
                    ignore=shutil.ignore_patterns("__pycache__"))
    policy = project / "research/cleanup-zero-base/whole"
    policy.mkdir(parents=True)
    write_json(policy / "allowed.json",
               {"allowed_axioms": [], "allowed_unproved": [{"name": "Fixture.kanQuillen_model_exists"}]})
    book = project / "research/fixture-coverage"
    book.mkdir()
    with (book / "items.csv").open("w", newline="") as stream:
        csv.writer(stream, lineterminator="\n").writerows([
            ["number", "status", "declarations", "reason", "reference_note"],
            ["1", "own", "Fixture.named @ SerrePositivity.lean:9", "name and statement test", ""],
            ["2", "partial", "", "empty declaration documented", "fixture only"],
        ])
    git(project, "init", "-q")
    git(project, "add", ".")
    git(project, "commit", "-qm", "Common source for coverage merge regression")

    external = out / "mathlib.json"
    write_json(external, dict(pin=pin, manifest=sha(manifest), toolchain=sha(project / "lean-toolchain"),
                              suffixes=["named"], rows=[]))

    def audit_tree(tree, label):
        mathlib = tree / ".lake/packages/mathlib"
        mathlib.parent.mkdir(parents=True, exist_ok=True)
        if not mathlib.is_symlink():
            mathlib.symlink_to(dependency, target_is_directory=True)
        run(tree, "lake", "build", "SerrePositivity")
        dest = out / f"{label}-record"
        run(tree, sys.executable, "scripts/audit2/audit.py", "run", str(dest))
        return dest / "audit.sqlite"

    baseline = audit_tree(project, "base")
    run(project, sys.executable, "scripts/audit2/coverage.py", "baseline",
        str(baseline), str(external), str(out / "baseline.json"))
    git(project, "add", "research/fixture-coverage/baseline.csv")
    git(project, "commit", "-qm", "Approve initial literature baseline")

    def verify(tree, database, label, expected, *flags):
        result = out / f"{label}.json"
        run(tree, sys.executable, "scripts/audit2/coverage_merge.py", str(database), str(external),
            str(result), "--baseline-ref", "HEAD", *flags, expected=expected)
        return json.loads(result.read_text())

    # The audit is keyed by HEAD. After storing the baseline, use a new receipt.
    healthy = audit_tree(project, "healthy")
    assert verify(project, healthy, "healthy", 0)["pass_"]
    if declaration_diff:
        def check_variant(label, source_after, status):
            tree = out / label
            git(project, "worktree", "add", "--detach", str(tree))
            (tree / "SerrePositivity.lean").write_text(source_after)
            git(tree, "add", "SerrePositivity.lean")
            git(tree, "commit", "-qm", label)
            mathlib = tree / ".lake/packages/mathlib"
            mathlib.parent.mkdir(parents=True, exist_ok=True)
            if not mathlib.is_symlink():
                mathlib.symlink_to(dependency, target_is_directory=True)
            run(tree, "lake", "build", "SerrePositivity")
            dest = out / f"{label}-comparison"
            run(tree, sys.executable, "scripts/audit2/premerge.py", str(healthy), str(external),
                str(dest), expected=status)
            return (json.loads((dest / "premerge.json").read_text()),
                    json.loads((dest / "diff/diff.json").read_text()))

        steps, diff = check_variant("deleted", source.replace("theorem named : bound ≤ 10 := by decide\n", ""), 1)
        assert steps["literature_executed"] and diff["counts"]["removed_required"] >= 1
        assert any(r["key"] == ["SerrePositivity", "Fixture.named"] for r in diff["removed"])
        steps, diff = check_variant("statement", source.replace("bound ≤ 10", "bound ≤ 11"), 1)
        assert steps["literature_executed"] and any(
            r["after"] == ["SerrePositivity", "Fixture.named"] and "type_hash" in r["fields"]
            for r in diff["changes"])
        steps, diff = check_variant("axiom", source.replace("end Fixture", "axiom newAxiom : True\nend Fixture"), 1)
        assert not steps["literature_executed"] and not diff["g2"]["no_new_axiom_or_sorry"]
        assert diff["g2"]["axiom_declarations"]["added"] == [["SerrePositivity", "Fixture.newAxiom"]]
        steps, diff = check_variant("instance", source.replace("end Fixture", "attribute [instance] availableSeed\n"
                                                             "instance addedInstance : Available := ⟨1⟩\nend Fixture"), 0)
        assert steps["pass_"] and any(r["after"] == ["SerrePositivity", "Fixture.availableSeed"] and
                                      "instances" in r["fields"] for r in diff["changes"])
        assert any(r["key"] == ["SerrePositivity", "Fixture.addedInstance"] and r["instances"] for r in diff["added"])
        steps, diff = check_variant("position", source.replace("theorem named", "\ntheorem named"), 0)
        assert steps["pass_"] and any(r["after"] == ["SerrePositivity", "Fixture.named"] and
                                      r.get("position_only") for r in diff["changes"])
        print("PASS: native deletion, changed statement, new axiom, new instance and position-only changes")
        return
    variants = [
        ("rename", "theorem named", "theorem renamed", "deleted", 1),
        ("statement", "bound ≤ 10", "bound ≤ 11", "statement-changed", 1),
        ("meaning", "bound : Nat := 0", "bound : Nat := 1", "meaning-changed", 3),
    ]
    for label, old, new, verdict, status in variants:
        tree = out / label
        git(project, "worktree", "add", "--detach", str(tree))
        (tree / "SerrePositivity.lean").write_text(SOURCE.replace(old, new))
        git(tree, "add", "SerrePositivity.lean")
        git(tree, "commit", "-qm", label)
        db = audit_tree(tree, label)
        result = verify(tree, db, label, status)
        change, = result["changes"]
        assert change["verdict"] == verdict and change["key"][1] == "1"
        if label == "meaning":
            a, b = change["old"], change["new"]
            approval = out / "approval.json"
            write_json(approval, [dict(file=b["file"], item=b["item"], ordinal=b["ordinal"],
                                       module=b["module"], name=b["name"],
                                       old_meaning=a["meaning_hash"], new_meaning=b["meaning_hash"])])
            assert verify(tree, db, "meaning-approved", 0, "--accept-meaning",
                          str(approval))["meaning_approved"] == 1
            assert verify(project, healthy, "unused-meaning-approval", 1, "--accept-meaning",
                          str(approval))["unused_approvals"]
    print("PASS: native rename and statement rejected; meaning requires exact approval")


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("output", type=Path)
    cli.add_argument("--declaration-diff", action="store_true")
    args = cli.parse_args()
    test(args.output.resolve(), args.declaration_diff)
