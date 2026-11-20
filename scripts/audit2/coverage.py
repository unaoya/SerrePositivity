#!/usr/bin/env python3
"""Resolve literature references and compare their recorded Lean statements."""
import argparse
from collections import Counter, defaultdict
import csv
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import subprocess
import time

from audit import (ROOT, Failure, Run, chunks, command, compile_worker, inventory,
                   json_line, read_locations, signature, write_json)

DECL = re.compile(r"(?:[^\W\d][\w'!?₀-₉]*|«[^»\n]+»)(?:\.(?:[\w'!?₀-₉]+|«[^»\n]+»))*\Z")
LIVE = {"own", "mathlib", "both", "partial", "interface"}
EDITIONS = {
    "bm18": "arXiv:1807.04725v4", "bs": "著者版", "bs17": "arXiv:1507.06490v3",
    "clmst": "arXiv:2209.04046v4", "dag13": "2011-12-15", "ha": "2017-09-18",
    "htt": "2017-04-09", "kerodon": "2026-11-06 取得", "ns": "arXiv:1707.01799v2",
    "paper": "2026-09-23", "rydh": "arXiv:0710.2488v3",
}
EXTERNAL_EDITIONS = {"BM18": EDITIONS["bm18"], "BS17": EDITIONS["bs17"],
                     "BS19": EDITIONS["bs"], "CLMST": EDITIONS["clmst"], "Rydh": EDITIONS["rydh"]}
FIELDS = ("literature item file line ordinal column raw status partial_kind edition reason reviewer "
          "resolution candidates module name type_hash meaning_hash location public commit baseline_note").split()
NOTE = "2026-11-20 初期基準（現行の主張を受け入れる。過去の照合時点の主張は未復元）"


def digest(data):
    return hashlib.sha256(json_line(data).encode()).hexdigest()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def entries(raw):
    return [part.strip() for part in raw.split(" | ") if part.strip()]


def spelling(raw):
    name, _, location = raw.partition(" @ ")
    name = re.split(r"（| \(", name, maxsplit=1)[0].strip()
    return name, location


def books(root):
    return sorted(root.glob("research/*-coverage"))


def read_tables(root):
    """Read active review sheets and their unreviewed item rows, plus K maps."""
    for book in books(root):
        literature = book.name.removesuffix("-coverage")
        reviewed = set()
        files = sorted((book / "review").glob("*.csv"))
        if literature == "k":
            files += sorted((book / "maps").glob("*/items.csv")) + [book / "maps/others.csv"]
        files += [book / "items.csv"]
        if literature == "paper":
            files += [book / "external.csv"]
        for path in files:
            with path.open(newline="", encoding="utf8") as stream:
                reader = csv.DictReader(stream)
                for row in reader:
                    number = row.get("number") or row.get("item") or ""
                    key = row.get("source") or row.get("reference") or ""
                    if path == book / "items.csv" and number in reviewed:
                        continue
                    if path.parent == book / "review":
                        reviewed.add(number)
                    status = row.get("status_new", row.get("status", "")) or ""
                    column = "declarations_new" if "declarations_new" in row else "declarations"
                    rel = path.relative_to(root).as_posix()
                    item = f"{key} {number}" if key else number
                    raw = row.get(column) or ""
                    edition = (EXTERNAL_EDITIONS.get(key) if path.name=="external.csv"
                               else EDITIONS.get(literature))
                    yield dict(literature=literature, item=item, file=rel, line=reader.line_num,
                               status=status, column=column, partial_kind=row.get("partial_kind", ""),
                               edition=row.get("edition") or edition or "版の記載なし",
                               reason=row.get("reason") or row.get("note") or "",
                               reviewer=row.get("reviewer") or "過去の照合者は記録なし",
                               reference_note=(row.get("reference_note") or "").strip(), raw=raw)


def load_db(path):
    db = sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True)
    db.row_factory = sqlite3.Row
    return db


def mathlib_pin(root):
    manifest = json.loads((root / "lake-manifest.json").read_text())
    rev = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    repo = root / ".lake/packages/mathlib"
    actual = subprocess.check_output(["git", "-C", repo, "rev-parse", "HEAD"], text=True).strip()
    if rev != actual:
        raise Failure("Mathlib checkout differs from the pinned manifest")
    if subprocess.check_output(["git", "-C", repo, "status", "--porcelain", "--untracked-files=no"]):
        raise Failure("Mathlib has tracked local modifications")
    return rev


def external(run, root):
    pin = mathlib_pin(root)
    requested = {spelling(e)[0].removeprefix("_root_.") for row in read_tables(root)
                 for e in entries(row["raw"])}
    suffixes = {n.rsplit(".", 1)[-1] for n in requested}
    worker = compile_worker(run, "Artifacts")
    package = root / ".lake/packages/mathlib"
    lib = package / ".lake/build/lib/lean"
    modules = sorted(p.relative_to(package).with_suffix("").as_posix().replace("/", ".")
                     for p in (package / "Mathlib").rglob("*.lean"))
    found = []
    for i, batch in enumerate(chunks(modules, 160)):
        paths = {m: lib / (m.replace(".", "/") + ".olean") for m in batch}
        inp = run.lines("external-targets.tsv", (f"{m}\t{p}" for m, p in paths.items()))
        raw = run.out / "external-batch.jsonl"
        run.execute(f"external-{i:03}", [worker, "extract", inp, raw])
        observed = set()
        with raw.open() as stream:
            for line in stream:
                row = json.loads(line)
                if len(row) == 3:
                    module = row[0]
                    observed.add(module)
                    locations = None
                    continue
                name = row[0]
                if name.rsplit(".", 1)[-1] not in suffixes:
                    continue
                if name in requested and locations is None:
                    locations = read_locations(paths[module].with_suffix(".ilean"), module)
                source = locations.get(name) if locations else None
                found.append(dict(module=module, name=name, type_hash=row[5], public=bool(row[2]),
                                  location=source, type_refs=row[7], kind=row[1]))
        if observed != set(batch):
            raise Failure("Mathlib extraction omitted a module")
        raw.unlink()
    if mathlib_pin(root) != pin:
        raise Failure("Mathlib checkout changed during extraction")
    write_json(run.out / "external.json", dict(pin=pin, modules=len(modules), suffixes=sorted(suffixes),
                                          toolchain=sha(root / "lean-toolchain"),
                                          manifest=sha(root / "lake-manifest.json"), rows=found))


class Index:
    def __init__(self, db, ext):
        self.db = db
        self.ext = defaultdict(list)
        self.external_suffix = defaultdict(list)
        self.pin = ext["pin"]
        self.modules = {name for name, in db.execute("SELECT name FROM module")}
        for r in ext["rows"]:
            self.ext[r["name"]].append(r)
            self.external_suffix[r["name"].rsplit(".",1)[-1]].append(r)
        self._suffix = None

    @lru_cache(maxsize=None)
    def exact(self, name):
        return [dict(r) for r in self.db.execute(
            "SELECT module,name,kind,type_hash,value_hash,type_refs,value_refs,ctors,location,public "
            "FROM decl WHERE name=? ORDER BY module", (name,))] + self.ext[name]

    def suffix(self, name):
        if self._suffix is None:
            self._suffix = defaultdict(list)
            for n, m in self.db.execute("SELECT name,module FROM decl"):
                self._suffix[n.rsplit(".", 1)[-1]].append((n, m))
        leaf = name.rsplit(".",1)[-1]
        c = self._suffix[leaf] + [(r["name"],r["module"]) for r in self.external_suffix[leaf]]
        return sorted((n,m) for n,m in c if n==name or n.endswith("."+name))

    def resolve(self, raw):
        name, path = spelling(raw)
        explicit = name.startswith("_root_.")
        name = name.removeprefix("_root_.")
        if not DECL.fullmatch(name):
            return "unreadable", None, []
        short = "." not in name and not explicit
        found = [] if short else self.exact(name)
        if len(found) == 1:
            row, = found
            supplied = re.search(r"(?:^|/)((?:SerrePositivity|Mathlib)(?:/[^:]+)?\.lean)(?::[0-9]+)?$", path)
            if path and not supplied and not path.startswith("SerrePositivity.lean:"):
                # Drafts or prose inputs must not be mistaken for an unrelated
                # library declaration with the same spelling.
                return "missing", None, [(row["name"], row["module"])]
            if supplied:
                owner = supplied[1].removesuffix(".lean").replace("/",".")
                if ".lake.packages.mathlib.Mathlib." in owner:
                    owner = "Mathlib." + owner.split(".lake.packages.mathlib.Mathlib.",1)[1]
                if owner.split(".")[0] != row["module"].split(".")[0] or (
                        owner in self.modules and owner != row["module"]):
                    return "missing", None, [(row["name"], row["module"])]
            return ("external" if row["module"].startswith("Mathlib.") else "unique"), row, []
        if found:
            return "ambiguous", None, [(r["name"],r["module"]) for r in found]
        candidates = self.suffix(name)
        return ("ambiguous" if len(candidates)>1 else "missing"), None, candidates[:30]

    @staticmethod
    def refs(row, key):
        value = row.get(key)
        return json.loads(value) if isinstance(value, str) else value or []

    @lru_cache(maxsize=None)
    def meaning(self, module, name):
        row = next(row for row in self.exact(name) if row["module"] == module)
        # The root's type is recorded separately. Traverse project definitions,
        # opaque values and the signatures of inductives and constructors.
        todo = list(self.refs(row, "type_refs"))
        visited = set()
        atoms = set()
        while todo:
            name = todo.pop()
            if name in visited:
                continue
            visited.add(name)
            for target in self.exact(name):
                if not target["module"].startswith("SerrePositivity"):
                    continue
                kind = target["kind"]
                if kind not in {"def", "opaque", "inductive", "ctor"}:
                    continue
                atoms.add((name, kind, target["type_hash"], target["value_hash"] or ""))
                todo.extend(self.refs(target, "type_refs"))
                todo.extend(self.refs(target, "value_refs"))
                todo.extend(self.refs(target, "ctors"))
        return digest([self.pin, sorted(atoms)])


def location(row):
    value = row["location"]
    if isinstance(value, str):
        value = json.loads(value)
    if not isinstance(value, list) or len(value) != 8 or not isinstance(value[4], int):
        return ""
    prefix = ".lake/packages/mathlib/" if row["module"].startswith("Mathlib.") else ""
    # Use the identifier's selection range. The command range can start at a
    # docstring or attribute on an earlier line.
    return f"{prefix}{row['module'].replace('.', '/')}.lean:{value[4] + 1}"


def resolve(root, db_file, external_file, old=(), moves=None):
    db = load_db(db_file)
    meta = dict(db.execute("SELECT key,value FROM metadata"))
    if meta["head"] != command(["git", "rev-parse", "HEAD"]):
        raise Failure("the record audit and working tree have different base commits")
    if command(["git", "status", "--porcelain", "--untracked-files=no", "--",
                "SerrePositivity.lean", "SerrePositivity", "lakefile.toml",
                "lake-manifest.json", "lean-toolchain"]):
        raise Failure("commit the candidate Lean inputs before running the coverage gate")
    if meta["signature"] != signature():
        raise Failure("the record audit was produced by different tools or dependencies")
    available = {name for name, in db.execute("SELECT name FROM module")}
    if set(inventory()[0]) != available:
        raise Failure("the record audit does not cover the tracked module inventory")
    sets = json.loads(db_file.with_name("sets.json").read_text())
    if any(set(sets[key]) != available for key in ("tracked", "built", "extracted", "checked")):
        raise Failure("the complete record audit receipt is required")
    ext = json.loads(external_file.read_text())
    if (ext["pin"] != mathlib_pin(root) or ext["manifest"] != sha(root/"lake-manifest.json")
            or ext["toolchain"] != sha(root/"lean-toolchain")):
        raise Failure("the external index has a different pinned input")
    items = list(read_tables(root))
    wanted = {spelling(entry)[0].rsplit(".", 1)[-1] for item in items
              for entry in entries(item["raw"])}
    missing_suffixes = wanted - set(ext["suffixes"])
    if missing_suffixes:
        raise Failure(f"refresh the Mathlib index for these new spellings: {sorted(missing_suffixes)[:12]}")
    index = Index(db, ext)
    verdicts, references, inputs = {}, [], {}
    prior = {identity(row):row for row in old}
    seen = set()
    for item in items:
        reference_note = item.pop("reference_note")
        path = item["file"]
        if path not in inputs:
            inputs[path] = sha(root/path)
        raw_entries = entries(item["raw"])
        if not raw_entries and item["status"] in LIVE and not reference_note:
            raw_entries = [""]
        for ordinal, raw in enumerate(raw_entries, 1):
            key = path, item["item"], ordinal
            if key in seen:
                raise Failure(f"duplicate item reference: {key}")
            seen.add(key)
            if raw not in verdicts:
                state, row, candidates = index.resolve(raw)
                verdict = dict(resolution=state, candidates=json_line(candidates))
                if row:
                    verdict.update(module=row["module"], name=row["name"], type_hash=row["type_hash"],
                                   meaning_hash=index.meaning(row["module"],row["name"]),
                                   location=location(row), public=row["public"])
                verdicts[raw] = verdict
            verdict = verdicts[raw]
            if moves and (previous := prior.get(key)) and previous["raw"] == raw:
                a = previous.get("module"), previous.get("name")
                if a in moves:
                    owner, name = moves[a]
                    state, row, candidates = index.resolve("_root_." + name)
                    if row and row["module"] == owner:
                        verdict = dict(resolution=state, candidates=json_line(candidates), module=owner,
                                       name=name, type_hash=row["type_hash"],
                                       meaning_hash=index.meaning(owner, name), location=location(row),
                                       public=row["public"])
                    else:
                        verdict = dict(resolution="missing", candidates=json_line(candidates))
            references.append(dict(item, raw=raw, ordinal=ordinal, **verdict))
    return dict(commit=meta["head"], inputs=inputs, references=references)


def baseline(path, plan):
    grouped = defaultdict(list)
    for row in plan["references"]:
        grouped[row["literature"]].append(row)
    for book in books(path):
        rows = grouped[book.name.removesuffix("-coverage")]
        with (book/"baseline.csv").open("w", encoding="utf8", newline="") as f:
            writer = csv.DictWriter(f, FIELDS, lineterminator="\n")
            writer.writeheader()
            writer.writerows(dict(r, commit=plan["commit"], baseline_note=NOTE) for r in rows)


def update_locations(root, plan, old, changes):
    edits = defaultdict(dict)
    prior = {identity(row):row for row in old}
    for change in changes:
        row = change["new"]
        if change["verdict"] not in {"location","approved-move"}:
            continue
        if not row["location"]:
            if change["verdict"] == "approved-move":
                raise Failure(f"no recorded position for approved move {change['key']}")
            continue
        raw_name, _, _ = row["raw"].partition(" @ ")
        if change["verdict"] == "approved-move":
            old_name, _ = spelling(row["raw"])
            new_name = ("_root_." if "." not in row["name"] else "") + row["name"]
            raw_name = new_name + raw_name[len(old_name):]
        raw = f"{raw_name} @ {row['location']}"
        edits[row["file"]][(row["line"],row["column"],int(row["ordinal"]))] = raw
        prior[identity(row)] = dict(row, raw=raw, commit=plan["commit"], baseline_note=NOTE)
    for path in edits:
        expected = plan.get("inputs", {}).get(path)
        if expected and sha(root/path) != expected:
            raise Failure(f"coverage source changed before location update: {path}")
    for path, replacements in edits.items():
        file = root/path
        with file.open(newline="", encoding="utf8") as stream:
            reader = csv.DictReader(stream)
            fields = reader.fieldnames
            rows = {reader.line_num: row for row in reader}
        for (line, column, ordinal), raw in replacements.items():
            parts = entries(rows[line][column])
            parts[ordinal - 1] = raw
            rows[line][column] = " | ".join(parts)
        newline = "\r\n" if b"\r\n" in file.read_bytes() else "\n"
        with file.open("w", newline="", encoding="utf8") as stream:
            writer = csv.DictWriter(stream, fields, lineterminator=newline)
            writer.writeheader()
            writer.writerows(rows.values())
    if edits:
        resolved_lines = {(r["file"],r["item"]): r["line"] for r in read_tables(root)}
        for row in prior.values():
            row["line"] = resolved_lines[(row["file"],row["item"])]
        grouped = defaultdict(list)
        for row in prior.values():
            grouped[row["literature"]].append(row)
        for book in books(root):
            with (book/"baseline.csv").open("w", newline="", encoding="utf8") as stream:
                writer = csv.DictWriter(stream, FIELDS, lineterminator="\n")
                writer.writeheader()
                writer.writerows(grouped[book.name.removesuffix("-coverage")])


def identity(row):
    return row["file"], row["item"], int(row["ordinal"])


def read_baselines(root):
    for book in books(root):
        with (book/"baseline.csv").open(newline="", encoding="utf8") as f:
            yield from csv.DictReader(f)


def compare(old, current, moves, strict):
    current = {identity(row):row for row in current}
    changes = []
    for row in old:
        key = identity(row)
        nxt = current.pop(key, None)
        resolved = row["resolution"] in {"unique", "external"}
        if nxt is None:
            verdict = "deleted"
        elif (row["status"], row["partial_kind"], row.get("reason"), row.get("edition")) != (
                nxt["status"], nxt["partial_kind"], nxt.get("reason"), nxt.get("edition")):
            verdict = "coverage-changed"
        elif not nxt.get("name"):
            verdict = "deleted" if resolved else ("existing-unresolved" if
                       (row["raw"],row["resolution"],row["candidates"]) ==
                       (nxt["raw"],nxt["resolution"],nxt["candidates"]) else "unresolved")
        elif not resolved:
            verdict = "newly-resolved"
        else:
            a, b = (row["module"], row["name"]), (nxt["module"], nxt["name"])
            if a != b and moves.get(a) != b:
                verdict = "unapproved-move"
            elif row["type_hash"] != nxt["type_hash"]:
                verdict = "statement-changed"
            elif row["meaning_hash"] != nxt["meaning_hash"]:
                verdict = "meaning-changed"
            elif a != b:
                verdict = "approved-move"
            elif nxt["location"] and (row["location"] != nxt["location"] or
                                      spelling(nxt["raw"])[1] != nxt["location"]):
                verdict = "location"
            else:
                continue
        changes.append(dict(key=key, verdict=verdict, old=row, new=nxt))
    for key, row in current.items():
        changes.append(dict(key=key, verdict="new-reference" if row.get("name") else "unresolved",
                            old=None, new=row))
    failures = {"deleted","unresolved","unapproved-move","coverage-changed","new-reference"}
    if strict:
        failures.update({"statement-changed","meaning-changed"})
    return dict(pass_=not any(r["verdict"] in failures for r in changes),
                changes=changes, counts=Counter(r["verdict"] for r in changes))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    p = sub.add_parser("external")
    p.add_argument("out", type=Path)
    for mode in ("resolve","baseline","check"):
        p = sub.add_parser(mode)
        p.add_argument("database", type=Path)
        p.add_argument("external", type=Path)
        p.add_argument("output", type=Path)
        if mode == "check":
            p.add_argument("--moves", type=Path)
            p.add_argument("--warn-fingerprints", action="store_true")
            p.add_argument("--apply-locations", action="store_true")
    args = parser.parse_args()
    start = time.monotonic()
    if args.mode == "external":
        external(Run(args.out), ROOT)
        return 0
    old, moves = [], {}
    if args.mode == "check":
        old = list(read_baselines(ROOT))
        if args.moves:
            for row in json.loads(args.moves.read_text()):
                a,b = tuple(row["old"]),tuple(row["new"])
                if a in moves or b in moves.values():
                    raise Failure("the approved move map must be one to one")
                moves[a] = b
    plan = resolve(ROOT,args.database,args.external,old,moves)
    plan["seconds"] = time.monotonic()-start
    if args.mode == "baseline":
        baseline(ROOT, plan)
    if args.mode == "check":
        result = compare(old, plan["references"], moves, not args.warn_fingerprints)
        if args.apply_locations and result["pass_"]:
            update_locations(ROOT, plan, old, result["changes"])
        result["seconds"] = time.monotonic()-start
        write_json(args.output,result)
        return int(not result["pass_"])
    write_json(args.output,plan)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (Failure, OSError, ValueError) as error:
        raise SystemExit(str(error))
