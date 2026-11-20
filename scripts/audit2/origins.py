#!/usr/bin/env python3
"""Classify declaration provenance without dropping private or ambiguous rows."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sqlite3

from audit import ROOT, Failure, command, connect_db, inventory, write_json

COMMAND = re.compile(
    r"^\s*(?:@\[[^]]*\]\s*)*"
    r"(?:(?:private|protected|public|noncomputable|unsafe|partial|nonrec|local|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|opaque|axiom|constant|inductive|structure|class|"
    r"instance|initialize|builtin_initialize)\b(?:\s+([^\s:({\[=]+))?"
)
GENERATED = re.compile(
    r"(?:\.match_\d|\._proof_\d|\.eq_\d|\._sparseCasesOn|\._sunfold|"
    r"\._unsafe_rec|\._hygCtx|\.congr_simp$|\._flat_ctor$|\.casesOn$|"
    r"\.recOn$|\.noConfusion(?:Type)?$)"
)


def classify(name, kind, location, lines):
    if kind in ("ctor", "rec"):
        return "kernel-generated"
    if location is not None:
        loc = json.loads(location)
        for i in (loc[4], loc[0]):
            if not 0 <= i < len(lines):
                continue
            match = COMMAND.match(lines[i])
            if match is None:
                continue
            keyword, token = match.groups()
            source_name = (token or "").removeprefix("_root_.")
            if source_name and (name == source_name or name.endswith("." + source_name)):
                return "source-command"
            if keyword == "instance" and not source_name:
                return "source-command"
    if GENERATED.search(name):
        return "kernel-generated"
    return "unclassified"


def record(table, out):
    if out.exists():
        raise Failure(f"choose a new output file: {out}")
    srcs, _ = inventory()
    db = connect_db(table)
    base = db.execute("SELECT value FROM metadata WHERE key='head'").fetchone()[0]
    if command(["git", "diff", "--name-only", base, "--", "SerrePositivity", "SerrePositivity.lean"]):
        raise Failure("the declaration locations are from a different main source tree")
    out.parent.mkdir(parents=True, exist_ok=True)
    counts = Counter()
    with sqlite3.connect(out) as res:
        res.execute("""CREATE TABLE origin(
            module TEXT NOT NULL, name TEXT NOT NULL, classification TEXT NOT NULL,
            partial_source INTEGER NOT NULL, PRIMARY KEY (module,name))""")
        current = None
        lines = []
        rows = []
        partial_helpers = {(m, n.removesuffix("._unsafe_rec")) for m, n in db.execute(
            "SELECT module,name FROM decl WHERE partial=1 AND name LIKE '%._unsafe_rec'")}
        for m, n, kind, loc, partial in db.execute(
                "SELECT module,name,kind,location,partial FROM decl ORDER BY module,name"):
            if m != current:
                lines = srcs[m].read_text().splitlines()
                current = m
            field = classify(n, kind, loc, lines)
            counts[field] += 1
            rows.append((m, n, field, int(partial or (m, n) in partial_helpers)))
            if len(rows) == 2000:
                res.executemany("INSERT INTO origin VALUES (?,?,?,?)", rows)
                rows.clear()
        res.executemany("INSERT INTO origin VALUES (?,?,?,?)", rows)
    write_json(out.with_suffix(".json"), dict(baseline=base, counts=counts, rows=sum(counts.values())))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path)
    parser.add_argument("origins", type=Path)
    args = parser.parse_args()
    record(args.table, args.origins)


if __name__ == "__main__":
    main()
