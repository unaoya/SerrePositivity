#!/usr/bin/env python3
"""Compare successively recorded Lean declarations using ownership-aware keys."""
import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
import tempfile
import time

from audit import ROOT, Failure, json_line, write_json
from coverage import load_db

COLUMNS = ("module", "name", "kind", "type_hash", "value_hash", "axioms", "instances",
           "location", "internal", "public", "private", "unsafe", "partial",
           "extern", "implemented_by")
AUXILIARY = re.compile(r"(?:^|\.)(_proof_\d+)$")
AUX_TOKEN = re.compile(r"(?<![\w'])(_proof_\d+)(?![\w'])")
INSTANCE = re.compile(
    r"^\s*(?:@\[[^]]*\]\s*)*(?:(?:private|public|protected|local|scoped|noncomputable|unsafe)\s+)*"
    r"instance\b\s*"
)
PRIORITY = re.compile(r"^\(\s*priority\s*:=")
ACTIVE = (
    "SerrePositivity.lean", "SerrePositivity", "scripts", "blueprint",
    ":(glob)research/*-coverage/items.csv", ":(glob)research/*-coverage/baseline.csv",
    ":(glob)research/*-coverage/statements.csv", ":(glob)research/*-coverage/external.csv",
    ":(glob)research/*-coverage/review/*.csv", ":(glob)research/k-coverage/maps/**/*.csv",
    ":(exclude)SerrePositivity/Archive", ":(exclude)scripts/archive", ":(exclude)scripts/refactor/targets",
)


def key(row):
    return row["module"], row["name"]


def area(module):
    return ".".join(module.split(".")[:3])


def cursor(db):
    return db.execute(f"SELECT {','.join(COLUMNS)} FROM decl ORDER BY module,name")


def metadata(db):
    result = dict(db.execute("SELECT key,value FROM metadata"))
    if not result.get("head") or not result.get("signature"):
        raise Failure("record missing its Git commit or acquisition signature")
    missing = db.execute("SELECT count(*) FROM decl WHERE axioms IS NULL").fetchone()[0]
    if missing:
        raise Failure(f"record has {missing} unknown axiom results")
    counts = dict(db.execute("SELECT name,declarations FROM module"))
    actual = dict(db.execute("SELECT module,count(*) FROM decl GROUP BY module"))
    if not counts or ({m: n for m, n in counts.items() if n} != actual):
        raise Failure("record declaration counts differ from its module inventory")
    return result


def read_head(commit):
    if not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", commit):
        raise Failure(f"record does not identify a full Git commit: {commit}")
    found = subprocess.run(["git", "cat-file", "-t", commit], cwd=ROOT, capture_output=True, text=True)
    if found.returncode or found.stdout.strip() != "commit":
        raise Failure(f"record commit is unavailable: {commit}")


@lru_cache(maxsize=512)
def source_lines(commit, module):
    path = module.replace(".", "/") + ".lean"
    result = subprocess.run(["git", "show", f"{commit}:{path}"], cwd=ROOT, capture_output=True, text=True)
    return result.stdout.splitlines() if result.returncode == 0 else []


def unnamed_position(commit, row):
    if row["instances"] == "[]" or row["location"] is None:
        return None
    loc = json.loads(row["location"])
    lines = source_lines(commit, row["module"])
    for line in {loc[0], loc[4]}:
        if not 0 <= line < len(lines):
            continue
        source = "\n".join(lines[line:min(len(lines), loc[2] + 1)])
        if match := INSTANCE.match(source):
            suffix = source[match.end():]
            if PRIORITY.match(suffix):
                level = 0
                for cursor, char in enumerate(suffix):
                    level += (char == "(") - (char == ")")
                    if level == 0:
                        suffix = suffix[cursor + 1:].lstrip()
                        break
                else:
                    continue
            if suffix and suffix[0] in ":({[⦃":
                return row["module"], loc[0], loc[1]
    return None


def by_identity(rows, make_key):
    grouped = defaultdict(list)
    for row in rows.values():
        if alt := make_key(row):
            grouped[alt].append(row)
    return grouped


def unique_pairs(before, after, get_before, get_after):
    a, b = by_identity(before, get_before), by_identity(after, get_after)
    for identity in sorted(a.keys() & b.keys()):
        if len(a[identity]) == len(b[identity]) == 1:
            yield a[identity][0], b[identity][0]


def axis(row, field):
    data = json.loads(row[field])
    if field == "axioms":
        return sorted(set(data))
    return sorted({tuple(item) for item in data}, key=json_line)


def changed_fields(old, new):
    changes = {}
    for field in COLUMNS[2:]:
        a, b = old[field], new[field]
        if a == b:
            continue
        if field in ("axioms", "instances"):
            a, b = axis(old, field), axis(new, field)
        elif field == "location":
            a, b = (json.loads(v) if v is not None else None for v in (a, b))
        if a != b:
            changes[field] = [a, b]
    return changes


def auxiliaries(rows):
    return {key(row): match[1] for row in rows if row["internal"] and row["location"] is None
            and (match := AUXILIARY.search(row["name"]))}


def text_uses(commits, candidates):
    if not candidates:
        return {}
    found = {}
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8") as patterns:
        patterns.write("".join(n + "\n" for n in sorted(candidates)))
        patterns.flush()
        for commit in sorted(set(commits)):
            proc = subprocess.Popen(
                ["git", "grep", "-n", "-I", "-F", "-z", "-f", patterns.name, commit, "--", *ACTIVE],
                cwd=ROOT, stdout=subprocess.PIPE, encoding="utf-8", errors="replace")
            with proc.stdout as stream:
                for line in stream:
                    path, lineno, source = line.split("\0", 2)
                    for match in AUX_TOKEN.finditer(source):
                        n = match[1]
                        if n in candidates and (commit, n) not in found:
                            found[commit, n] = [path.removeprefix(commit + ":"), int(lineno)]
            if proc.wait() not in (0, 1):
                raise Failure(f"could not search active sources at {commit}")
    return found


def unpaired_row(row):
    return dict(key=list(key(row)), kind=row["kind"], type_hash=row["type_hash"],
                axioms=axis(row, "axioms"), instances=axis(row, "instances"),
                location=json.loads(row["location"]) if row["location"] is not None else None)


def g2_sets(db):
    def collect(sql, params=()):
        return {tuple(row) for row in db.execute(sql, params)}
    return {
        "axiom_declarations": collect("SELECT module,name FROM decl WHERE kind='axiom'"),
        "sorry_dependencies": collect('SELECT module,name FROM decl WHERE instr(axioms, ?) > 0', ('"sorryAx"',)),
        "direct_sorry": collect(
            """SELECT module,name FROM decl WHERE name = 'sorryAx' OR instr(type_refs, ?) > 0
               OR instr(value_refs, ?) > 0 OR instr(ctors, ?) > 0""", ('"sorryAx"',) * 3),
    }


def axioms_used(db):
    return {name for (name,) in db.execute("SELECT DISTINCT value FROM decl, json_each(decl.axioms)")}


def compare(before, after, out, layout=False):
    start = time.monotonic()
    a_meta, b_meta = metadata(before), metadata(after)
    if a_meta["signature"] != b_meta["signature"]:
        raise Failure("the records have different Lean acquisition signatures")
    commits = [a_meta["head"], b_meta["head"]]
    for commit in set(commits):
        read_head(commit)
    out.mkdir(parents=True, exist_ok=True)
    added, removed, changed = {}, {}, []
    areas = defaultdict(Counter)
    equivalent = {}
    retained_count = 0
    fingerprint = hashlib.sha256()
    with (out / "retained.jsonl").open("w") as retained:
        def pair(a, b, match):
            nonlocal retained_count
            old, new = key(a), key(b)
            changes = changed_fields(a, b)
            if match != "exact":
                equivalent[old] = new
            if match != "exact" or changes:
                record = dict(before=old, after=new, match=match, fields=changes)
                changed.append(record)
                target = areas[area(new[0])]
                if match != "exact":
                    target[match] += 1
                if match == "exact" and changes.keys() == {"location"}:
                    target["position_only"] += 1
                    record["position_only"] = True
                for field in ("type_hash", "axioms", "instances", "value_hash"):
                    if field in changes:
                        target[field] += 1
            if a["type_hash"] == b["type_hash"] and a["name"] == b["name"]:
                line = json_line([*old, new[0], a["type_hash"]]) + "\n"
                retained.write(line)
                fingerprint.update(line.encode("utf-8"))
                retained_count += 1

        a_rows, b_rows = cursor(before), cursor(after)
        a, b = next(a_rows, None), next(b_rows, None)
        while a is not None or b is not None:
            if b is None or (a is not None and key(a) < key(b)):
                removed[key(a)] = a
                a = next(a_rows, None)
            elif a is None or key(b) < key(a):
                added[key(b)] = b
                b = next(b_rows, None)
            else:
                pair(a, b, "exact")
                a, b = next(a_rows, None), next(b_rows, None)

        common = {n for _, n in removed} & {n for _, n in added}
        unique = {n for n in common if all(
            db.execute("SELECT count(*) FROM decl WHERE name=?", (n,)).fetchone()[0] == 1
            for db in (before, after))}
        for a, b in unique_pairs(removed, added, lambda row: row["name"] if row["name"] in unique else None,
                                 lambda row: row["name"] if row["name"] in unique else None):
            pair(a, b, "owner_changed")
            del removed[key(a)], added[key(b)]
        for a, b in unique_pairs(removed, added, lambda row: unnamed_position(commits[0], row),
                                 lambda row: unnamed_position(commits[1], row)):
            pair(a, b, "unnamed_instance")
            del removed[key(a)], added[key(b)]

    candidates = auxiliaries([*removed.values(), *added.values()]) if layout else {}
    uses = text_uses(commits, set(candidates.values()))
    unpaired = {}
    auxiliary_counts = Counter()
    for side, rows in (("removed", removed), ("added", added)):
        items = []
        for k, row in sorted(rows.items()):
            item = unpaired_row(row)
            item["category"] = "required"
            if suffix := candidates.get(k):
                refs = [[commit, *uses[commit, suffix]] for commit in sorted(set(commits)) if (commit, suffix) in uses]
                if refs:
                    item["active_reference"] = refs
                else:
                    item["category"] = "auxiliary"
                    auxiliary_counts[side] += 1
            areas[area(k[0])][side + "_" + item["category"]] += 1
            if item["instances"]:
                areas[area(k[0])][side + "_with_instance"] += 1
            items.append(item)
        unpaired[side] = items

    g2_before, g2_after = g2_sets(before), g2_sets(after)
    g2 = {}
    for field in g2_before:
        original, newer = g2_before[field], g2_after[field]
        projected = {equivalent.get(k, k) for k in original}
        g2[field] = dict(before=len(original), after=len(newer), added=sorted(newer - projected),
                         removed=sorted(k for k in original if equivalent.get(k, k) not in newer))
    new_dependencies = [
        [*row["after"], sorted(set(row["fields"]["axioms"][1]) - set(row["fields"]["axioms"][0]))]
        for row in changed if "axioms" in row["fields"] and
        set(row["fields"]["axioms"][1]) - set(row["fields"]["axioms"][0])
    ]
    g2["new_axiom_dependencies_of_paired_declarations"] = new_dependencies
    old_axioms, new_axioms = axioms_used(before), axioms_used(after)
    g2["axiom_names_used"] = dict(before=sorted(old_axioms), after=sorted(new_axioms),
                                added=sorted(new_axioms - old_axioms), removed=sorted(old_axioms - new_axioms))
    totals = Counter({name: 0 for name in (
        "removed_required", "added_required", "removed_auxiliary", "added_auxiliary", "owner_changed",
        "unnamed_instance", "position_only", "type_hash", "value_hash", "axioms", "instances",
        "added_with_instance", "removed_with_instance")})
    for values in areas.values():
        totals.update(values)
    g2["no_new_axiom_or_sorry"] = not (
        new_dependencies or g2["axiom_names_used"]["added"] or any(g2[name]["added"] for name in g2_before))
    preserved = not (totals["removed_required"] or totals["added_required"] or totals["type_hash"])
    result = dict(before=commits[0], after=commits[1], layout=layout,
                  retained_name_and_type=dict(count=retained_count, sha256=fingerprint.hexdigest(),
                                              rows="retained.jsonl"),
                  names_and_types_preserved=preserved, counts=totals, by_area=dict(sorted(areas.items())),
                  auxiliary=auxiliary_counts, changes=changed, g2=g2, **unpaired,
                  seconds=time.monotonic() - start)
    write_json(out / "diff.json", result)
    return result


def run():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("before", type=Path)
    p.add_argument("after", type=Path)
    p.add_argument("out", type=Path)
    p.add_argument("--layout", action="store_true", help="check source usage before exempting internal proof names")
    a = p.parse_args()
    with load_db(a.before) as before, load_db(a.after) as after:
        diff = compare(before, after, a.out, a.layout)
    print(json_line(dict(counts=diff["counts"], g2=diff["g2"]["no_new_axiom_or_sorry"], seconds=diff["seconds"])))


if __name__ == "__main__":
    try:
        run()
    except (Failure, OSError, ValueError, sqlite3.Error) as error:
        print(f"audit diff: {error}", file=sys.stderr)
        sys.exit(2)
