#!/usr/bin/env python3
"""Build inventory, saved Lean artifacts, and independent axiom verification."""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import time

TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parents[1]
LIB = ROOT / ".lake/build/lib/lean"
POLICY = ROOT / "research/cleanup-zero-base/whole/allowed.json"
LAKE = ["lake", "env", "lean"]
BATCH = 160
SCHEMA = """
CREATE TABLE metadata (key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE module (
    name TEXT PRIMARY KEY, trace TEXT NOT NULL, imports TEXT NOT NULL,
    declarations INTEGER NOT NULL);
CREATE TABLE decl (
    module TEXT NOT NULL, name TEXT NOT NULL, kind TEXT NOT NULL,
    public INTEGER NOT NULL, private INTEGER NOT NULL, internal INTEGER NOT NULL,
    type_hash TEXT NOT NULL, value_hash TEXT, type_refs TEXT NOT NULL,
    value_refs TEXT NOT NULL, ctors TEXT NOT NULL, saved_axioms TEXT,
    instances TEXT NOT NULL, unsafe INTEGER NOT NULL, implemented_by TEXT,
    extern INTEGER NOT NULL, partial INTEGER NOT NULL, location TEXT,
    axioms TEXT, source TEXT, PRIMARY KEY (module, name)
);
CREATE INDEX decl_by_name ON decl(name);
"""
DECL_COLUMNS = """module,name,kind,public,private,internal,type_hash,value_hash,
    type_refs,value_refs,ctors,saved_axioms,instances,unsafe,implemented_by,
    extern,partial,location,axioms,source"""


class Failure(Exception):
    pass


class FileLimit(Failure):
    pass


def json_line(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def command(args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


class Run:
    def __init__(self, out):
        self.out = Path(out).resolve()
        self.out.mkdir(parents=True, exist_ok=True)
        self.started = time.time()
        self.receipts = []
        if q := os.getenv("AUDIT2_QUEUED_AT"):
            self.queue_seconds = self.started - float(q)
        else:
            self.queue_seconds = None

    def execute(self, label, args):
        log = self.out / f"{label}.log"
        started = time.monotonic()
        with log.open("w") as output:
            process = subprocess.run(
                ["/usr/bin/time", "-l", *map(str, args)], cwd=ROOT,
                stdout=output, stderr=subprocess.STDOUT,
            )
        seconds = time.monotonic() - started
        self.receipts.append(dict(label=label, seconds=seconds, rc=process.returncode))
        self.save_times()
        if process.returncode:
            if "Too many open files in system" in log.read_text(errors="replace"):
                raise FileLimit(f"{label}: environmental ENFILE; retry alone ({log})")
            raise Failure(f"{label}: exit {process.returncode} ({log})")

    def save_times(self):
        write_json(self.out / "timings.json", dict(
            wait=self.queue_seconds, elapsed=time.time() - self.started, jobs=self.receipts))

    def lines(self, name, values):
        output = self.out / name
        output.write_text("".join(f"{v}\n" for v in values))
        return output


def inventory():
    result = {}
    excluded = Counter()
    for source in command(["git", "ls-files", "-z", "--", "*.lean"]).rstrip("\0").split("\0"):
        if source == "SerrePositivity.lean" or source.startswith("SerrePositivity/"):
            if source.startswith("SerrePositivity/Archive/"):
                excluded["Archive"] += 1
                continue
            name = source.removesuffix(".lean").replace("/", ".")
            if name in result:
                raise Failure(f"duplicate tracked module {name}")
            result[name] = ROOT / source
        else:
            excluded[source.split("/", 1)[0]] += 1
    if not result:
        raise Failure("empty tracked module inventory")
    return result, excluded


def build(run, chosen, verify):
    target_file = run.lines("targets.txt", sorted(chosen))
    options = ["--rehash", "--no-cache"]
    if verify:
        options.append("--no-build")
    worker = compile_worker(run, "Build")
    run.execute("preflight-lake" if verify else "build", ["lake", "env", worker,
                                                       target_file, *options])


def compile_worker(run, name):
    source = TOOLS / f"{name}.lean"
    c_file = run.out / f"{name}.c"
    binary = run.out / name
    run.execute(f"compile-{name}", [*LAKE, "-c", c_file, source])
    linkage = ["-lLake"] if name in ("Build", "Artifacts") else []
    run.execute(f"link-{name}", ["lake", "env", "leanc", "-O2", "-rdynamic", "-o", binary, c_file, *linkage])
    return binary


def artifact_path(name):
    return LIB / (name.replace(".", "/") + ".olean")


def describe(name):
    base = artifact_path(name)
    trace = base.with_suffix(".trace")
    data = json.loads(trace.read_text())
    outputs = data["outputs"]
    suffixes = [".olean", ".olean.server", ".olean.private"] if outputs["m"] else [".olean"]
    hashes = outputs["o"] if isinstance(outputs["o"], list) else [outputs["o"]]
    if len(hashes) != len(suffixes) or not data.get("depHash"):
        raise Failure(f"{name}: unexpected Lake trace format")
    paths = [(base.with_suffix(s), h) for s, h in zip(suffixes, hashes)]
    paths.append((base.with_suffix(".ilean"), outputs["i"]))
    expected = []
    for path, output in paths:
        if not path.is_file() or not isinstance(output, str):
            raise Failure(f"{name}: missing output or missing hash {path}")
        digest, *rest = output.split(".", 1)
        if len(digest) != 16 or any(c not in "0123456789abcdef" for c in digest):
            raise Failure(f"{name}: malformed trace hash {output}")
        expected.append((path, digest))
    return trace, data["depHash"], expected


def file_stamp(path):
    # Another worktree can replace its link to this inode during a build.
    # Compare the bytes available at this path through a single open handle.
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            size += len(block)
            digest.update(block)
    return size, digest.hexdigest()


def preflight(run, selected, sources, worker):
    stamps = {}
    expected = []
    traces = {}
    for name in sorted(selected):
        try:
            trace, inputs, artifacts = describe(name)
            traces[name] = json_line([inputs, [h for _, h in artifacts]])
            expected.extend(artifacts)
            for p in [sources[name], trace, *(a for a, _ in artifacts)]:
                stamps[p] = file_stamp(p)
        except (OSError, ValueError, KeyError, TypeError) as error:
            raise Failure(f"{name}: cannot validate Lake trace/artifacts: {error}") from error
    build(run, selected, verify=True)
    checks = run.lines("artifact-hashes.tsv", (f"{p}\t{h}" for p, h in expected))
    run.execute("preflight-artifact-hashes", [worker, "hashes", checks])
    assert_stamps(stamps)
    return traces, stamps


def assert_stamps(stamps):
    for path, before in stamps.items():
        try:
            now = file_stamp(path)
        except OSError as error:
            raise Failure(f"preflight input disappeared: {path}") from error
        if now != before:
            raise Failure(f"preflight input changed during audit: {path}")


def signature():
    h = hashlib.sha256()
    for path in [ROOT / "lean-toolchain", ROOT / "lake-manifest.json", ROOT / "lakefile.toml",
                 TOOLS / "Artifacts.lean", TOOLS / "Oracle.lean", TOOLS / "audit.py"]:
        h.update(path.read_bytes())
    h.update(command(["lean", "--version"]).encode())
    h.update(command(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]).encode())
    if command(["git", "-C", ".lake/packages/mathlib", "status", "--porcelain", "--untracked-files=no"]):
        raise Failure("Mathlib has tracked local modifications")
    return h.hexdigest()


def read_locations(path, owner):
    # The ilean stores references as well as declaration locations. Read just
    # enough for the leading declaration map, which is much smaller.
    dec = json.JSONDecoder()
    with path.open() as stream:
        text = stream.read(65536)
        marker = '"decls":'
        if marker not in text:
            raise Failure(f"{owner}: invalid ilean declaration index")
        prefix = text.index(marker) + len(marker)
        while True:
            try:
                return dec.raw_decode(text[prefix:].lstrip())[0]
            except json.JSONDecodeError:
                more = stream.read(65536)
                if not more:
                    raise Failure(f"{owner}: incomplete ilean declaration index") from None
                text += more


def ingest(db, path, expected, traces):
    modules = {}
    buffer = []
    owner = None

    def finish():
        if owner is not None and count != declared:
            raise Failure(f"{owner}: scanned {count} rows, expected {declared}")

    with path.open() as raw:
        for line in raw:
            entry = json.loads(line)
            if len(entry) == 3:
                finish()
                owner, imports, declared = entry
                if owner not in expected or owner in modules:
                    raise Failure(f"unexpected or repeated module {owner}")
                modules[owner] = True
                db.execute("INSERT INTO module VALUES (?,?,?,?)",
                           (owner, traces[owner], json_line(imports), declared))
                positions = read_locations(artifact_path(owner).with_suffix(".ilean"), owner)
                count = 0
            else:
                if owner is None or len(entry) != 16:
                    raise Failure(f"invalid declaration record {entry[:2]}")
                count += 1
                for i in (7, 8, 9, 10, 11):
                    entry[i] = None if entry[i] is None else json_line(entry[i])
                saved = entry[10]
                location = positions.get(entry[0])
                buffer.append((owner, *entry, json_line(location) if location else None,
                               saved, None if saved is None else "stored"))
                if len(buffer) == 2000:
                    db.executemany("INSERT INTO decl VALUES (" + ",".join(["?"] * 20) + ")", buffer)
                    buffer.clear()
    finish()
    if set(modules) != set(expected):
        raise Failure(f"missing modules from artifact extract: {sorted(set(expected) - set(modules))[:20]}")
    db.executemany("INSERT INTO decl VALUES (" + ",".join(["?"] * 20) + ")", buffer)


def chunks(values, size):
    for start in range(0, len(values), size):
        yield values[start:start + size]


def imports_of(db):
    return {m: json.loads(deps) for m, deps in db.execute("SELECT name, imports FROM module")}


def closure(graph, initial):
    visited = set()
    todo = list(initial)
    while todo:
        top = todo.pop()
        if top in visited:
            continue
        visited.add(top)
        todo.extend(graph.get(top, ()))
    return visited


def oracle_groups(graph, targets, limit):
    # Topologically ordered roots usually keep the closure compact. For the
    # root itself a single closure is unavoidable. Other groups limit the
    # union of project imports, with a separate machine-pressure check.
    todo = set(targets)
    if "SerrePositivity" in graph:
        whole = closure(graph, ["SerrePositivity"])
        if len(whole) <= limit and len(todo & whole) >= 1000:
            yield ["SerrePositivity"], todo & whole
            todo -= whole
    while todo:
        roots = []
        reached = set()
        for owner in sorted(todo, key=lambda m: (m.count("."), m), reverse=True):
            if owner in reached or (owner == "SerrePositivity" and len(todo) > 1):
                continue
            deps = closure(graph, [owner])
            if roots and len(reached | deps) > limit:
                continue
            roots.append(owner)
            reached.update(deps)
            if len(roots) == 2500:
                break
        covered = todo & reached
        yield roots, covered
        todo -= covered


def wait_for_resources(run, tag, project_count, exclusive):
    if sys.platform != "darwin":
        return
    started = time.monotonic()
    tmp = Path(os.getenv("TMPDIR", "/tmp"))
    log = run.out / (tag + ".resources")
    # Count a conservative Mathlib/core closure in addition to project imports.
    needed = 4 * (project_count + 8500) + 8000
    while True:
        other = []
        for name in ("serre-lake-build.lock", "serre-lake-build.lock.1"):
            try:
                owner = json.loads((tmp / name / "owner.json").read_text())
            except (OSError, ValueError):
                continue
            if owner.get("worktree") != str(ROOT):
                other.append(owner.get("worktree"))
        info = command(["sysctl", "kern.maxvnodes", "kern.num_vnodes", "kern.free_vnodes",
                        "kern.maxfiles", "kern.num_files"])
        resource = {key: int(value) for key, value in (line.split(": ") for line in info.splitlines())}
        with log.open("a") as out:
            out.write(json_line(dict(system=resource, other=other, estimate=needed)) + "\n")
        vnodes = resource["kern.maxvnodes"] - resource["kern.num_vnodes"] + resource["kern.free_vnodes"]
        files = resource["kern.maxfiles"] - resource["kern.num_files"]
        if min(vnodes, files) >= needed and (not exclusive or not other):
            run.receipts.append(dict(label=tag + "-resource-wait", seconds=time.monotonic() - started, rc=0))
            return
        if time.monotonic() - started > 600:
            raise Failure(f"{tag}: no safe import window; resume in an isolated bulk window ({log})")
        time.sleep(10)


def oracle(run, worker, graph, targets, mode, limit):
    label = "slow" if mode == "all" else "fallback"
    for i, (roots, covered) in enumerate(oracle_groups(graph, targets, limit)):
        tag = f"{label}-{i:03}"
        rootfile = run.lines(tag + ".roots", roots)
        wanted = run.lines(tag + ".wanted", (row for m in sorted(covered) for row in targets[m]))
        result = run.out / (tag + ".jsonl")
        args = ["lake", "env", worker, rootfile, wanted, result, mode]
        project_count = len(closure(graph, roots))
        wait_for_resources(run, tag, project_count, exclusive=project_count >= 18000)
        try:
            run.execute(tag, args)
        except FileLimit:
            (run.out / (tag + ".log")).rename(run.out / (tag + ".enfile.log"))
            wait_for_resources(run, tag + "-retry", project_count, exclusive=True)
            run.execute(tag + "-retry", args)
        yield result, covered


def fill(db, run, worker, graph, limit):
    requests = defaultdict(list)
    for m, n in db.execute("SELECT module,name FROM decl WHERE axioms IS NULL ORDER BY module,name"):
        requests[m].append(f"{m}\t{n}")
    for path, covered in oracle(run, worker, graph, requests, "missing", limit):
        seen = set()
        for row in map(json.loads, path.open()):
            if len(row) == 2:
                continue
            m, n, axs, how = row
            key = m, n
            updated = db.execute("UPDATE decl SET axioms=?, source=? WHERE module=? AND name=? AND axioms IS NULL",
                                 (json_line(sorted(set(axs))), how, m, n)).rowcount
            if not updated or key in seen or m not in covered:
                raise Failure(f"unexpected fallback result: {key}")
            seen.add(key)
        if len(seen) != sum(len(requests[m]) for m in covered):
            raise Failure(f"missing fallback results in {path}")
        db.commit()
    unknown = db.execute("SELECT count(*) FROM decl WHERE axioms IS NULL").fetchone()[0]
    if unknown:
        raise Failure(f"{unknown} declarations without a Lean axiom result")


def connect_db(path):
    db = sqlite3.connect(path)
    db.row_factory = sqlite3.Row
    return db


def collect(run, sources, selected, previous, limit, resume=False):
    sig = signature()
    worker = compile_worker(run, "Artifacts")
    traces, stamps = preflight(run, selected, sources, worker)
    target = run.out / "audit.sqlite"
    partial = target.with_suffix(".partial")
    if target.exists() or (partial.exists() and not resume):
        raise Failure(f"choose a new output directory: {target}")
    restoring = partial.exists()
    with connect_db(partial) as db:
        pending = set(selected)
        if restoring:
            prior = db.execute("SELECT value FROM metadata WHERE key='signature'").fetchone()
            if prior is None or prior[0] != sig:
                raise Failure("resume table has a different toolchain, dependency or tool version")
            for name, trace in db.execute("SELECT name,trace FROM module"):
                if name not in pending or traces[name] != trace:
                    raise Failure(f"resume receipt differs for {name}")
                pending.remove(name)
        else:
            db.executescript(SCHEMA)
            db.execute("INSERT INTO metadata VALUES ('signature', ?)", (sig,))
            db.execute("INSERT INTO metadata VALUES ('head', ?)", (command(["git", "rev-parse", "HEAD"]),))
        if previous and not restoring:
            state = Path(previous).resolve().parent / "corroboration.json"
            if state.is_file() and not json.loads(state.read_text())["pass_"]:
                raise Failure("the previous table is suspended after a corroboration failure")
            db.execute("ATTACH DATABASE ? AS previous", (str(Path(previous).resolve()),))
            prior = db.execute("SELECT value FROM previous.metadata WHERE key='signature'").fetchone()
            if prior is None or prior[0] != sig:
                raise Failure("previous table has a different toolchain, dependency or schema signature")
            for m, trace in db.execute("SELECT name,trace FROM previous.module"):
                if m in pending and trace == traces[m]:
                    db.execute("INSERT INTO module SELECT * FROM previous.module WHERE name=?", (m,))
                    db.execute(f"INSERT INTO decl ({DECL_COLUMNS}) SELECT {DECL_COLUMNS} FROM previous.decl WHERE module=?", (m,))
                    pending.remove(m)
        for i, batch in enumerate(chunks(sorted(pending), BATCH)):
            inp = run.lines("extract-input.tsv", (f"{m}\t{artifact_path(m)}" for m in batch))
            raw = run.out / "extract-output.jsonl"
            run.execute(f"extract-{i:03}", [worker, "extract", inp, raw])
            ingest(db, raw, batch, traces)
            db.commit()
            raw.unlink()
        graph = imports_of(db)
        if db.execute("SELECT EXISTS(SELECT 1 FROM decl WHERE axioms IS NULL)").fetchone()[0]:
            if previous and any(m not in selected for deps in graph.values() for m in deps if m in sources):
                raise Failure("previous-table reuse for a partial corpus requires its project import closure")
            fill(db, run, compile_worker(run, "Oracle"), graph, limit)
        assert_stamps(stamps)
        if signature() != sig:
            raise Failure("toolchain or dependency configuration changed during audit")
        if set(graph) != set(selected):
            raise Failure("tracked and extracted module sets differ")
    partial.rename(target)
    write_json(run.out / "sets.json", dict(tracked=sorted(selected), built=sorted(traces),
                                         extracted=sorted(graph), refreshed=sorted(pending)))
    return target

def parent_name(name):
    # Same grouping as scripts/refactor/audit_sorries.lean.
    if name.startswith("_private."):
        parts = name.split(".")
        boundary = next((i for i, part in enumerate(parts[1:], 1) if part.isdecimal()), None)
        if boundary is not None:
            name = ".".join(parts[boundary + 1:])
    pieces = name.split(".")
    while len(pieces) > 1 and (pieces[-1].isdecimal() or pieces[-1].startswith(
            ("_proof_", "match_", "_match_", "proof_", "_aux_"))):
        pieces.pop()
    return ".".join(pieces)


def evaluate(run, path, selected, require_main):
    db = connect_db(path)
    start = time.monotonic()
    policy = json.loads(POLICY.read_text())
    allowed = set(policy["allowed_axioms"])
    inputs = {x["name"] for x in policy["allowed_unproved"]}
    main = "SerrePositivity.main_statement"
    kan = next(n for n in inputs if n.endswith(".kanQuillen_model_exists"))
    failures = []
    kinds = Counter()
    evidence = Counter()
    areas = Counter()
    declarations = Counter()
    unchecked = set()
    sorry = set()
    direct = {}
    ax_violations = []
    sorry_users = defaultdict(set)

    for row in db.execute("SELECT * FROM decl"):
        key = row["module"], row["name"]
        kinds[row["kind"]] += 1
        declarations[row["module"]] += 1
        if row["axioms"] is None:
            unchecked.add(row["module"])
            failures.append(f"unknown axioms: {key}")
            continue
        evidence[row["source"]] += 1
        axs = set(json.loads(row["axioms"]))
        refs = (set(json.loads(row["type_refs"])) | set(json.loads(row["value_refs"])) |
                set(json.loads(row["ctors"])))
        if extra := axs - allowed - {"sorryAx"}:
            ax_violations.append([*key, sorted(extra)])
        if "sorryAx" in refs or row["name"] == "sorryAx":
            parent = parent_name(row["name"])
            direct[key] = parent
            if "sorryAx" not in axs:
                failures.append(f"{key}: direct sorry missing from Lean's result")
        if "sorryAx" in axs:
            sorry.add(key)
            areas[".".join(row["module"].split(".")[:3])] += 1
            for n in refs:
                sorry_users[n].add(key)
    modules = {r[0]: r[1] for r in db.execute("SELECT name,declarations FROM module")}
    checked = {m for m, n in modules.items() if declarations[m] == n and m not in unchecked}
    if checked != set(selected):
        failures.append(f"module mismatch: missing {sorted(set(selected) - checked)[:30]}, "
                        f"extra {sorted(checked - set(selected))[:30]}")
    if ax_violations:
        failures.append(f"{len(ax_violations)} declarations use an unapproved axiom")
    actual = set(direct.values())
    if unexpected := actual - inputs:
        failures.append(f"unapproved direct sorry parents: {sorted(unexpected)}")
    if require_main and (missing := inputs - actual):
        failures.append(f"allowed input without a directly observed sorry: {sorted(missing)}")

    witnesses = {}
    attributable = set()
    for parent in sorted(inputs):
        seeds = {k for k, p in direct.items() if p == parent}
        seen = set()
        todo = list(seeds)
        while todo:
            k = todo.pop()
            if k in seen:
                continue
            seen.add(k)
            todo.extend(sorry_users[k[1]] - seen)
        attributable.update(seen)
        witnesses[parent] = dict(
            direct=sorted(seeds), reached=len(seen), area_counts=Counter(
                ".".join(m.split(".")[:3]) for m, _ in seen),
            reaches_main=any(n == main for _, n in seen))
    unexplained = sorted(sorry - attributable)
    if unexplained:
        failures.append(f"{len(unexplained)} sorry dependencies without an allowed input path")
    if require_main:
        if db.execute("SELECT count(*) FROM decl WHERE name=?", (main,)).fetchone()[0] != 1:
            failures.append("main theorem is absent or ambiguous")
        main_inputs = {parent for parent, v in witnesses.items() if v["reaches_main"]}
        if main_inputs != inputs - {kan}:
            failures.append(f"main theorem input mismatch: {sorted(main_inputs)}")
    result = dict(pass_=not failures, failures=failures, checked=sorted(checked),
                  declarations=sum(kinds.values()), kinds=kinds, axiom_origins=evidence,
                  unknown=sum(kinds.values()) - sum(evidence.values()), extra_axioms=ax_violations,
                  sorry_declarations=len(sorry), direct_sorry=sorted([*k, p] for k, p in direct.items()),
                  sorry_by_area=areas, inputs=witnesses, unattributed_sorry=unexplained,
                  seconds=time.monotonic() - start)
    write_json(run.out / "g2.json", result)
    sets_file = run.out / "sets.json"
    if sets_file.exists():
        sets = json.loads(sets_file.read_text())
        sets["checked"] = sorted(checked)
        if any(sets.get(k) != sets["tracked"] for k in ("built", "extracted", "checked")):
            failures.append("tracked, built, extracted and checked sets differ")
            result["pass_"] = False
            write_json(run.out / "g2.json", result)
        write_json(sets_file, sets)
    return result


def corroborate(run, path, sources, limit):
    db = connect_db(path)
    graph = imports_of(db)
    if set(graph) != set(sources):
        raise Failure("full comparison needs exactly the tracked main module set")
    sig = db.execute("SELECT value FROM metadata WHERE key='signature'").fetchone()[0]
    if sig != signature():
        raise Failure("table is from a different tool or dependency version")
    hashes = compile_worker(run, "Artifacts")
    traces, stamps = preflight(run, set(sources), sources, hashes)
    if traces != dict(db.execute("SELECT name,trace FROM module")):
        raise Failure("the saved table does not describe the validated artifacts")
    worker = compile_worker(run, "Oracle")
    expected = { (m, n): None if a is None else set(json.loads(a))
                 for m, n, a in db.execute("SELECT module,name,axioms FROM decl") }
    hits = set()
    parts = set()
    differences = []
    counts = Counter()
    for result, covered in oracle(run, worker, graph, {n: [n] for n in graph}, "all", limit):
        have = set()
        for row in map(json.loads, result.open()):
            if len(row) == 2:
                m, n = row
                if m in parts or m not in covered:
                    raise Failure(f"unexpected repeated module in oracle: {m}")
                have.add(m)
                parts.add(m)
                continue
            m, n, axs, how = row
            key = m, n
            if key not in expected or key in hits or m not in covered:
                raise Failure(f"extra or repeated oracle key: {key}")
            hits.add(key)
            counts[how] += 1
            if expected[key] != set(axs):
                previous = expected[key]
                differences.append([m, n, None if previous is None else sorted(previous), sorted(set(axs)), how])
        if have != covered:
            raise Failure(f"oracle module omission: {sorted(covered - have)[:15]}")
    missing = sorted(expected.keys() - hits)
    assert_stamps(stamps)
    result = dict(pass_=not missing and not differences and parts == set(graph),
                  expected=len(expected), compared=len(hits), modules=len(parts),
                  oracle_modes=counts, missing=missing, differences=differences)
    write_json(run.out / "comparison.json", result)
    write_json(path.parent / "corroboration.json", dict(pass_=result["pass_"],
                                                       evidence=str(run.out / "comparison.json")))
    return result


def validate_selected(args, sources):
    chosen = set(Path(args.modules).read_text().splitlines()) if args.modules else set(sources)
    if not chosen or not chosen <= sources.keys():
        raise Failure(f"invalid module selection: {sorted(chosen - sources.keys())[:20]}")
    return chosen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    for mode in ("build", "run", "compare", "inventory"):
        p = sub.add_parser(mode)
        p.add_argument("out")
        if mode in ("run", "build"):
            p.add_argument("--modules", help="limit to an explicitly selected partial corpus")
        if mode in ("run", "compare"):
            p.add_argument("--limit", type=int, default=16500, help="known import closure budget per oracle group")
        if mode == "run":
            p.add_argument("--previous", help="reuse verified rows with unchanged Lake traces")
            p.add_argument("--resume", action="store_true", help="resume a verified partial checkpoint")
        if mode == "compare":
            p.add_argument("table")
    args = parser.parse_args()
    run = Run(args.out)
    try:
        sources, excluded = inventory()
        tracked = validate_selected(args, sources) if args.mode in ("run", "build") else set(sources)
        run.lines("inventory.txt", sorted(sources))
        write_json(run.out / "inventory.json", dict(main=len(sources), excluded=excluded,
                                                     selected=len(tracked)))
        if args.mode == "build":
            build(run, tracked, verify=False)
        if args.mode == "run":
            path = collect(run, sources, tracked, args.previous, args.limit, args.resume)
            return 0 if evaluate(run, path, tracked, tracked == sources.keys())["pass_"] else 1
        if args.mode == "compare":
            return 0 if corroborate(run, args.table, sources, args.limit)["pass_"] else 1
    except (Failure, OSError, sqlite3.Error, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        return 2
    finally:
        run.save_times()
    return 0


if __name__ == "__main__":
    sys.exit(main())
