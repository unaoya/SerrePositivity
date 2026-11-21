#!/usr/bin/env python3
"""Run the record audit, declaration diff, and literature baseline gate."""
import argparse
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import time

from audit import ROOT, TOOLS, Failure, write_json
from coverage import load_db


def pipeline(args):
    start = time.monotonic()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    with load_db(args.before) as db:
        found = db.execute("SELECT value FROM metadata WHERE key='head'").fetchone()
    if not found:
        raise Failure("baseline record has no Git commit")
    baseline_ref = args.baseline_ref or found[0]
    candidate = out / "record" / "audit.sqlite"
    if candidate.exists() or candidate.with_suffix(".partial").exists():
        raise Failure(f"choose a new output directory: {out}")
    steps = {}

    def step(name, *command):
        beginning = time.monotonic()
        log = out / f"{name}.log"
        with log.open("w") as stream:
            status = subprocess.run(
                [sys.executable, TOOLS / command[0], *command[1:]],
                cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT).returncode
        steps[name] = dict(status=status, seconds=time.monotonic() - beginning, log=log.name)
        return status

    record = step("record-audit", "audit.py", "run", out / "record",
                  "--previous", args.before.resolve())
    # A complete table with a failed G2 verdict still explains what changed.
    disk_complete = candidate.is_file() and candidate.with_name("g2.json").is_file()
    diff = None
    literature = None
    if disk_complete and record in (0, 1):
        diff = step("declaration-diff", "diff.py", args.before.resolve(), candidate, out / "diff",
                    *(["--layout"] if args.layout else []))
        if record == 0 and diff == 0:
            approval = ["--accept-meaning", args.accept_meaning.resolve()] if args.accept_meaning else []
            literature = step("literature-gate", "coverage_merge.py", candidate, args.mathlib.resolve(),
                              out / "literature.json", "--baseline-ref", baseline_ref, *approval)
    result = dict(pass_=record == diff == literature == 0, baseline_ref=baseline_ref, steps=steps,
                  diff_available=diff == 0, literature_executed=literature is not None,
                  seconds=time.monotonic() - start)
    write_json(out / "premerge.json", result)
    print(json.dumps(result, ensure_ascii=False))
    return (record or diff or literature or 0) if disk_complete else (record or 2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("mathlib", type=Path, help="index for the pinned Mathlib")
    parser.add_argument("out", type=Path)
    parser.add_argument("--baseline-ref")
    parser.add_argument("--accept-meaning", type=Path)
    parser.add_argument("--layout", action="store_true")
    return pipeline(parser.parse_args())


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (Failure, OSError, ValueError, sqlite3.Error) as error:
        print(f"premerge: {error}", file=sys.stderr)
        sys.exit(2)
