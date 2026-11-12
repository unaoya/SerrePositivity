#!/usr/bin/env python3
"""Recompute declaration evidence from chapter reviews and preview assignment changes."""

import argparse
from collections import defaultdict
import csv
from pathlib import Path
import re
import sys


IC = "SerrePositivity/InfinityCategories/"
SOURCE = re.compile(r"(.+?) @ (SerrePositivity/[^:\s]+\.lean)(?::\d+)?")
PLACEMENT_STATUSES = {"own", "both", "mathlib"}
STATUSES = PLACEMENT_STATUSES | {"partial", "none"}
PARTIAL_PLACEMENTS = {"partial", "partial+topic"}
RETAINED_PARTIAL = "previous partial-based placement retained"


def numbers(text):
    return tuple(map(int, text.split(".")))


def section(number):
    return ".".join(number.split(".")[:2])


def read_rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def load_reviews(items, directory, complete=True):
    expected = defaultdict(set)
    for row in items:
        expected[numbers(row["number"])[0]].add(row["number"])
    result = {}
    for chapter, wanted in sorted(expected.items()):
        path = directory / f"ch{chapter}.csv"
        if not path.is_file() and not complete:
            continue
        rows = read_rows(path)
        if len(rows) != len(wanted) or {r["number"] for r in rows} != wanted:
            raise ValueError(f"{path}: missing, extra, or duplicate item numbers")
        for r in rows:
            verdict, status = r["verdict"], r["status_new"]
            if (verdict not in ("ok", "fix", "unsure", "partial") or status not in STATUSES
                    or (verdict == "partial" and status != "partial")):
                raise ValueError(f"{path}: invalid verdict or status for {r['number']}")
            result[r["number"]] = r
    return result


def check_review_gate(reviews, directory, accepted):
    if not accepted:
        raise ValueError("final refresh requires --accept-cross-review after reading the cross reports")
    check = directory / "check"
    missing = [f"cross report for Ch {ch}" for ch in range(1, 11)
               if not (check / f"cross-{ch}.md").is_file()
               and not any(p.is_file() for p in check.glob(f"cross-{ch}-*.md"))]
    for chapter in range(2, 11):
        if not (check / f"ch{chapter}-kernel-evidence.json").is_file():
            missing.append(f"ch{chapter}-kernel-evidence.json")
        if not any((check / f"ch{chapter}-none-search.{ext}").is_file() for ext in ("json", "jsonl")):
            missing.append(f"ch{chapter}-none-search.json or .jsonl")
    if missing:
        raise ValueError("missing review evidence or cross reports: " + ", ".join(missing))
    shallow = [n for n, row in reviews.items() if row["status_new"] in PLACEMENT_STATUSES
               and row["verdict"] != "unsure" and not re.search(r"仮定[:：].+結論[:：].+", row["reason"], re.S)]
    if shallow:
        raise ValueError(f"hypothesis/conclusion evidence missing on {len(shallow)} rows: {shallow[:8]}")


def get_evidence(items, reviews):
    evidence, pending = defaultdict(list), defaultdict(set)
    for item in items:
        n = item["number"]
        reviewed = reviews.get(n)
        sources = item["declarations"]
        status = item["status"]
        basis = "items"
        if reviewed:
            status = reviewed["status_new"]
            sources = reviewed["declarations_new"]
            basis = "review"
        if reviewed and reviewed["verdict"] == "unsure":
            for citation in (sources + " | " + item["declarations"]).split(" | "):
                if match := SOURCE.fullmatch(citation):
                    pending[match[2]].add(n)
            continue
        if status not in PLACEMENT_STATUSES or numbers(n)[1] == 0:
            continue
        for citation in sources.split(" | "):
            if match := SOURCE.fullmatch(citation):
                evidence[match[2]].append((n, match[1], status, basis))
    return evidence, pending


def toc_sections(toc):
    # Derive the paths from the same English headings used in the first proposal.
    def camel(title):
        title = title.replace(r"$\operatorname{\mathcal{QC}}$", "QC")
        title = re.sub(r"\$\\operatorname\{Ex\}\^\{\\infty\s*\}\$", "Ex Infinity", title)
        title = re.sub(r"\$\\infty\s*\$", "Infinity", title).replace("$2$", "Two")
        return "".join(word[0].upper() + word[1:] for word in re.findall(r"[A-Za-z]+", title))

    chapters = {}
    sections = {}
    for line in toc.splitlines():
        if match := re.fullmatch(r"- Chapter (\d+) \[\w+\] (.+)", line):
            chapters[match[1]] = camel(match[2])
        if match := re.fullmatch(r"  - (\d+\.\d+) \[(\w+)\] (.+)", line):
            number, tag, title = match.groups()
            sections[number] = IC + "Kerodon/" + chapters[number.split(".")[0]] + "/" + camel(title), tag
    return sections


def refresh(rows, items, reviews, sections, approved_external=()):
    evidence, pending = get_evidence(items, reviews)
    refreshed, changes = [], []
    known = {row["source"] for row in rows}
    if len(known) != len(rows):
        raise ValueError("duplicate source in assignment")
    approved_external = set(approved_external)
    for original in rows:
        row = original.copy()
        row["partial_placement_retained"] = ""
        path = row["source"]
        if row["scope"] == "documentation":
            refreshed.append(row)
            continue
        prior = row["section"]
        hits = defaultdict(list)
        for entry in evidence.get(path, []):
            if section(entry[0]) in sections:
                hits[section(entry[0])].append(entry)
        source_notes = []
        if pending.get(path):
            source_notes.append("unsure items " + " ".join(sorted(pending[path], key=numbers)))
        if row["evidence"] in PARTIAL_PLACEMENTS:
            # Retain the Stage 1 row as historical evidence for this placement.
            row["partial_placement_retained"] = "yes"
            source_notes.append(RETAINED_PARTIAL)
        elif hits:
            def score(s):
                entries = hits[s]
                strong = {n for n, _, status, _ in entries if status in {"own", "both"}}
                cited = {n for n in row["docstring_refs"].split() if section(n) == s}
                return (-len(strong), -len({entry[0] for entry in entries}), -len(cited), s != prior, numbers(s))

            best = min(hits, key=score)
            selected = hits[best]
            confirmed = any(entry[-1] == "review" for entry in selected)
            row["basis"] = "review" if confirmed else "items"
            row["evidence"] = "declaration"
            if best != prior:
                directory, tag = sections[best]
                row["section"], row["section_tag"] = best, tag
                row["proposed_path"] = f"{directory}/{Path(row['proposed_path']).name}"
            def format_hits(entries):
                return " | ".join(f"{n}:{name} ({status}, {basis})"
                                  for n, name, status, basis in sorted(set(entries), key=lambda e: (numbers(e[0]), e[1])))
            row["declarations"] = format_hits(selected)
            row["declaration_items"] = " ".join(sorted({entry[0] for entry in selected}, key=numbers))
            row["other_declarations"] = format_hits(entry for s, es in hits.items() if s != best for entry in es)
            doc_sections = {section(n) for n in row["docstring_refs"].split() if section(n) in sections}
            row["other_sections"] = " ".join(sorted((doc_sections | hits.keys()) - {best}, key=numbers))
            own_by_section = {s: {e[1] for e in es if e[2] in ("own", "both")} for s, es in hits.items()}
            split = own_by_section[best] and any(
                names - own_by_section[best] for s, names in own_by_section.items() if s != best)
            if split:
                source_notes.append("distinct own/both declarations in multiple sections")
            if row["scope"] == "inside" and (confirmed or split):
                row["action"] = "split-proposed" if split else "main-section" if row["other_sections"] else "move"
        else:
            row["basis"] = "items"
            if row["declarations"] or row["other_declarations"]:
                row["declarations"] = row["declaration_items"] = row["other_declarations"] = ""
                row["evidence"] = "review-no-correspondence"
                row["other_sections"] = " ".join(sorted(
                    {section(n) for n in row["docstring_refs"].split() if section(n) in sections} - {prior},
                    key=numbers))
                if row["scope"] == "inside":
                    row["action"] = "placement-review"
                source_notes.append("previous declaration evidence withdrawn; verify placement")
        if row["scope"] == "external-candidate":
            eligible = (path in approved_external and not row["action"].startswith("hold-")
                        and row["section"] == prior and not pending.get(path)
                        and row["evidence"] != "review-no-correspondence")
            row["move_approved"] = "yes" if eligible else "no"
            if path in approved_external and not eligible:
                source_notes.append("approved external path needs review before moving")
        else:
            row["move_approved"] = ""
        if prior != row["section"] or original["basis"] != row["basis"] or source_notes:
            changes.append(change(path, original, row, "; ".join(source_notes)))
        refreshed.append(row)
    for path in sorted(evidence.keys() - known):
        new_sections = sorted({section(e[0]) for e in evidence[path]}, key=numbers)
        changes.append(change(path, {}, {"section": " ".join(new_sections)}, "new source; assign manually"))
    destinations = defaultdict(list)
    for row in refreshed:
        destinations[row["proposed_path"]].append(row)
    for dest, conflicts in destinations.items():
        if len(conflicts) > 1:
            for row in conflicts:
                changes.append(change(row["source"], row, row, f"destination collision: {dest}"))
    return refreshed, changes


def change(source, before, after, reason):
    return {
        "source": source, "old_section": before.get("section", ""), "new_section": after.get("section", ""),
        "old_basis": before.get("basis", ""), "new_basis": after.get("basis", ""),
        "old_path": before.get("proposed_path", ""), "new_path": after.get("proposed_path", ""), "reason": reason,
    }


def write_rows(path, rows, fields):
    with path.open("x", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assignment", type=Path, required=True)
    parser.add_argument("--coverage", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--approved-external", type=Path, help="exact approved source paths, one per line")
    parser.add_argument("--allow-incomplete", action="store_true", help="interim preview for available chapters")
    parser.add_argument("--accept-cross-review", action="store_true",
                        help="confirm the cross reports and any required rechecks were accepted")
    args = parser.parse_args()
    try:
        items = read_rows(args.coverage / "items.csv")
        reviews = load_reviews(items, args.coverage / "review", not args.allow_incomplete)
        if not args.allow_incomplete:
            check_review_gate(reviews, args.coverage / "review", args.accept_cross_review)
        rows = read_rows(args.assignment)
        approved = set(args.approved_external.read_text().split()) if args.approved_external else set()
        if approved - {r["source"] for r in rows if r["scope"] == "external-candidate"}:
            raise ValueError("approved external path missing from candidate table")
        refreshed, changes = refresh(rows, items, reviews,
                                     toc_sections((args.coverage / "toc.md").read_text()),
                                     () if args.allow_incomplete else approved)
        args.output_dir.mkdir()
        write_rows(args.output_dir / "assignment.csv", refreshed, [*rows[0], "partial_placement_retained", "move_approved"])
        write_rows(args.output_dir / "changes.csv", changes, list(change("", {}, {}, "")))
        status = "interim preview" if args.allow_incomplete else "review gate acknowledged"
        print(f"{status}: {len(reviews)} reviewed items, {len(refreshed)} assignments, {len(changes)} changes")
    except (KeyError, ValueError, OSError) as error:
        print(error, file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
