#!/usr/bin/env python3
"""Check a candidate against the literature baseline after the record audit."""
import argparse
import csv
import io
import json
from pathlib import Path
import subprocess
import sys

from audit import Failure, ROOT, command, write_json
from coverage import compare, identity, read_baselines, resolve


def baseline_at(ref):
    commit = command(["git", "rev-parse", "--verify", "--end-of-options", f"{ref}^{{commit}}"])
    paths = command(["git", "ls-tree", "-r", "--name-only", commit, "--", "research"]).splitlines()
    baselines = [path for path in paths if Path(path).match("research/*-coverage/baseline.csv")]
    if not baselines:
        raise Failure(f"no literature baselines in {commit}")
    for path in baselines:
        data = command(["git", "show", f"{commit}:{path}"])
        yield from csv.DictReader(io.StringIO(data))


def meaning_change(change):
    old, new = change["old"], change["new"]
    return (*change["key"], new["module"], new["name"],
            old["meaning_hash"], new["meaning_hash"])


def approval_key(row):
    return (*identity(row), row["module"], row["name"], row["old_meaning"], row["new_meaning"])


def gate(old, current, approved):
    for title, records in (("baseline", old), ("candidate", current)):
        keys = {identity(row) for row in records}
        if len(keys) != len(records):
            raise Failure(f"duplicate literature keys in {title}")
    result = compare(old, current, {}, strict=True)
    meaning = [change for change in result["changes"] if change["verdict"] == "meaning-changed"]
    # An owner or name change is a move, never an approval of meaning alone.
    used = {meaning_change(change) for change in meaning} & approved
    pending = [change for change in meaning if meaning_change(change) not in used]
    for change in meaning:
        change["meaning_approved"] = meaning_change(change) in used
    hard = [c for c in result["changes"] if c["verdict"] not in {"location", "meaning-changed"}]
    unused = sorted(approved - used)
    blockers = bool(hard or unused)
    result.update(pass_=not (blockers or pending), hard_failures=hard, meaning_review=pending,
                  meaning_approved=len(used), unused_approvals=unused,
                  exit_code=1 if blockers else 3 if pending else 0)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("database", type=Path, help="complete, successful record audit")
    parser.add_argument("mathlib", type=Path, help="index for the pinned Mathlib")
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--baseline-ref", help="read baselines from the pre-merge commit")
    parser.add_argument("--accept-meaning", type=Path, help="JSON list of approved meaning changes")
    args = parser.parse_args()
    approvals = json.loads(args.accept_meaning.read_text()) if args.accept_meaning else []
    approved = {approval_key(row) for row in approvals}
    if len(approved) != len(approvals):
        raise Failure("duplicate meaning approvals")
    g2 = json.loads(args.database.with_name("g2.json").read_text())
    if not g2["pass_"]:
        raise Failure("record audit failed")
    old = list(baseline_at(args.baseline_ref) if args.baseline_ref else read_baselines(ROOT))
    plan = resolve(ROOT, args.database, args.mathlib)
    result = gate(old, plan["references"], approved)
    result.update(commit=plan["commit"], baseline_ref=args.baseline_ref)
    write_json(args.receipt, result)
    print(f"hard failures {len(result['hard_failures'])}, pending meaning {len(result['meaning_review'])}, "
          f"approved meaning {result['meaning_approved']}; {args.receipt}")
    return result["exit_code"]


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (Failure, OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as error:
        print(f"coverage merge check: {error}", file=sys.stderr)
        raise SystemExit(2) from error
