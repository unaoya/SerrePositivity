#!/usr/bin/env python3
"""Collect Lean references, preview namespace edits, and select external aliases."""

import argparse
from bisect import bisect_right
from collections import defaultdict
from datetime import date
from graphlib import CycleError, TopologicalSorter
import json
from hashlib import sha256
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory

from klw1_layer_check import IC, IMPORT
from layer_check import code_only, under


PART = r"(?:[^\W\d][\w']*|«[^»\r\n]+»)"
IDENT = re.compile(rf"{PART}(?:\.{PART})*")
PARTS = re.compile(PART)
HERE = Path(__file__).resolve().parent


def read_json(path):
    return json.loads(path.read_text())


def write_json(path, value):
    with path.open("x") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def file_list(path):
    rows = read_json(path)
    if not isinstance(rows, list) or len(rows) != len(set(rows)):
        raise ValueError("expected a JSON array of distinct Lean paths")
    for p in rows:
        if not isinstance(p, str) or p != Path(p).as_posix() or Path(p).is_absolute() or ".." in Path(p).parts or not p.endswith(".lean"):
            raise ValueError(f"invalid relative Lean path: {p}")
        module_name(p)
    if len({module_name(p) for p in rows}) != len(rows):
        raise ValueError("paths collide as Lean module names")
    return sorted(rows)


def validate_name(name):
    if not IDENT.fullmatch(name) or name.startswith("_root_."):
        raise ValueError(f"invalid absolute Lean name: {name}")
    return name


def module_name(path):
    parts = Path(path).with_suffix("").parts
    if any(any(c in part for c in "«»\r\n") for part in parts):
        raise ValueError(f"unsupported module path: {path}")
    return ".".join(part if re.fullmatch(r"[^\W\d][\w']*", part) else f"«{part}»"
                    for part in parts)


def collect(root, sources, output, lean=None):
    root = root.resolve()
    output.mkdir()
    command = [str(lean.resolve())] if lean else ["lake", "env", "lean"]
    lake_project = any((root / name).is_file() for name in ("lakefile.toml", "lakefile.lean"))
    # A concurrent tool release must not change the helper halfway through a run.
    helper_source = (HERE / "klw1_collect_refs.lean").read_bytes()
    with TemporaryDirectory(prefix="klw1-collect-") as directory:
        tmp = Path(directory)
        helper = tmp / "klw1_collect_refs.lean"
        helper.write_bytes(helper_source)
        for path in sources:
            module = module_name(path)
            capture = tmp / "refs.json"
            args = [*command, "--run", str(helper), module, path, str(capture)]
            setup_hash = None
            if lake_project:
                # Lake supplies current package/library options, visibility and plugins.
                # Missing dependencies fail explicitly, without an implicit build.
                result = subprocess.run(["lake", "--no-build", "setup-file", path],
                                        cwd=root, capture_output=True, text=True)
                if result.stderr:
                    sys.stderr.write(result.stderr)
                if result.returncode:
                    if result.stdout:
                        sys.stderr.write(result.stdout)
                    raise ValueError(f"{path}: Lake setup failed; build dependencies before collect")
                setup = tmp / "setup.json"
                setup.write_text(result.stdout)
                setup_hash = sha256(setup.read_bytes()).hexdigest()
                args.append(str(setup))
            subprocess.run(args, cwd=root, check=True)
            data = checked_capture(root, path, capture)
            data.setdefault("elaboration", {}).update(
                collector_sha256=sha256(helper_source).hexdigest(), lake_setup_sha256=setup_hash)
            (output / (module + ".json")).write_text(json.dumps(data, ensure_ascii=False))
    write_json(output / "files.json", sources)


def checked_capture(root, path, capture):
    data = read_json(capture)
    actual = (root / path).read_bytes()
    if (data["schema_version"] != 1 or data["module"] != module_name(path)
            or data["source"].encode() != actual):
        raise ValueError(f"{path}: Lean capture does not match the exact source")
    return data


def captures(root, sources, directory):
    index = file_list(directory / "files.json")
    if index != sorted(sources):
        raise ValueError(f"{directory}: scan coverage differs from the requested manifest")
    for path in sources:
        data = checked_capture(root, path, directory / (module_name(path) + ".json"))
        yield path, data


def private_user_name(owner, name):
    prefix = f"_private.{owner}."
    if name.startswith(prefix):
        return re.sub(r"^[0-9]+\.", "", name[len(prefix):], count=1)
    return name


def rename_prefix(name, table):
    if name == "[anonymous]":
        return ""
    keys = [old for old in table if under(name, old)]
    if not keys:
        return name
    key = max(keys, key=len)
    return table[key] + name[len(key):]


class Migration:
    def __init__(self, plan):
        self.modules = plan.get("modules", {})
        self.namespaces = plan.get("namespaces", {})
        self.opens = plan.get("opens", {})
        self.module_opens = plan.get("module_opens", {})
        self.existing_aliases = plan.get("existing_aliases", {})
        self.symbols = {}
        self.field_exports = defaultdict(list)
        export_names = set()
        self.namespace_origins = {old for table in self.namespaces.values()
                                  for old, new in table.items() if old != new}
        public = defaultdict(list)
        for row in plan["rows"]:
            old, new = row["old"], validate_name(row["new"])
            owner = validate_name(row["module"])
            private = old.startswith("_private.")
            validate_name(private_user_name(owner, old))
            key = owner, old
            if key in self.symbols:
                raise ValueError(f"duplicate symbol: {key}")
            if new == old:
                raise ValueError(f"identity rename: {key}")
            if not private:
                public[old].append(row)
            self.symbols[key] = row
            if receiver := row.get("field_namespace"):
                receiver = validate_name(receiver)
                new_parent, _, leaf = new.rpartition(".")
                exported = f"{receiver}.{leaf}"
                if (private or not new_parent or leaf != old.rsplit(".", 1)[-1]
                        or exported == new or exported in export_names):
                    raise ValueError(f"invalid or ambiguous field export: {key} -> {exported}")
                self.field_exports[owner].append((old, new_parent, receiver, leaf))
                export_names.add(exported)
        # A name alone can be ambiguous across isolated module environments.
        # Keep the fallback only when there is one possible definition.
        self.public_symbols = {old: rows[0] for old, rows in public.items() if len(rows) == 1}
        self.old_public = set(public)
        destinations = [row["new"] for row in self.symbols.values() if not row["old"].startswith("_private.")]
        if len(destinations) != len(set(destinations)):
            raise ValueError("duplicate public destination")
        if export_names.intersection(destinations):
            raise ValueError("field export shadows a canonical name")
        if self.old_public.intersection(destinations):
            raise ValueError("old public names overlap new public destinations")
        for old, new in self.modules.items():
            validate_name(old)
            validate_name(new)
        if len(set(self.modules.values())) != len(self.modules):
            raise ValueError("duplicate module destination")
        for module, mapping in self.namespaces.items():
            validate_name(module)
            for old, new in mapping.items():
                validate_name(old)
                validate_name(new)
        for module, policies in self.module_opens.items():
            validate_name(module)
            for old, new in policies.items():
                validate_name(old)
                if new is not None:
                    validate_name(new)
        for old, new in self.opens.items():
            validate_name(old)
            if new is not None:
                validate_name(new)
        for old, new in self.existing_aliases.items():
            validate_name(old)
            validate_name(new)

    def target(self, ref):
        return self.symbols.get((ref["module"], ref["name"]))


def rewrite(data, migration):
    """Return a preview and diagnostics. No preview is returned for a blocked file."""
    source = data["source"].encode()
    module = data["module"]
    ns_map = migration.namespaces.get(module, {})
    opens = migration.opens | migration.module_opens.get(module, {})
    edits, diagnostics = {}, []
    guarded = []
    refs = defaultdict(list)
    moved_blocks = []
    changed_opens = set()
    def check_span(row):
        a, b = row["start"], row["stop"]
        if not 0 <= a < b <= len(source):
            raise ValueError(f"{module}: invalid byte span {a}:{b}")
        return a, b

    def spelling(row):
        a, b = check_span(row)
        return source[a:b].decode()

    def block(row, reason):
        diagnostics.append({"start": row["start"], "stop": row["stop"], "reason": reason})

    def edit(row, replacement):
        key = check_span(row)
        if spelling(row) == replacement:
            return
        if key in edits and edits[key] != replacement:
            block(row, "competing edits")
        edits[key] = replacement

    def relative(name, parent):
        if not parent:
            return name
        if name.startswith(parent + "."):
            return name[len(parent) + 1:]
        return None

    for ref in data["refs"]:
        refs[check_span(ref)].append(ref)

    commands = sorted((r for r in data["commands"] if "start" in r), key=lambda r: r["start"])
    simple_opens = defaultdict(list)
    for row in commands:
        if row["kind"] == "open" and row["mode"] == "simple" and "start" in row["command"]:
            simple_opens[check_span(row["command"])].append(row)
    removed_opens = set()
    for (lo, hi), operands in simple_opens.items():
        removed = [r for r in operands if len(r["names"]) == 1
                   and opens.get(r["names"][0], r["names"][0]) is None]
        if not removed:
            continue
        spans = [check_span(r) for r in operands]
        line = source.rfind(b"\n", 0, lo) + 1
        if (spans[0][0] != lo or spans[-1][1] != hi
                or not re.fullmatch(rb"[ \t]*open[ \t]+", source[line:lo])
                or any(not re.fullmatch(rb"[ \t]+", source[a:b])
                       for (_, a), (b, _) in zip(spans, spans[1:]))):
            continue
        if len(removed) == len(operands):
            edit({"start": line, "stop": hi}, "")
        else:
            for row in removed:
                start, stop = check_span(row)
                while start > line and source[start - 1:start] in (b" ", b"\t"):
                    start -= 1
                edit({"start": start, "stop": stop}, "")
        removed_opens.update(check_span(r) for r in removed)
        changed_opens.update(r["names"][0] for r in removed)

    for row in commands:
        kind = row["kind"]
        if kind == "namespace":
            new = rename_prefix(row["name"], ns_map)
            parent = rename_prefix(row["parent"], ns_map)
            written = relative(new, parent)
            if not written:
                block(row, f"cannot nest {new} in {parent}")
            elif written != spelling(row):
                edit(row, written)
                moved_blocks.append((row["before"], row["after"], written))
        elif kind == "end":
            if row["before"] <= row["after"]:
                continue
            labels = PARTS.findall(spelling(row))
            for lo, hi, replacement in reversed(moved_blocks):
                if hi <= row["after"] or row["before"] <= lo:
                    continue
                if lo < row["after"] or hi > row["before"]:
                    block(row, "partial close of a renamed multi-part namespace")
                    continue
                start = lo - row["after"]
                stop = hi - row["after"]
                labels[start:stop] = [replacement]
            if labels:
                edit(row, ".".join(labels))
            moved_blocks = [b for b in moved_blocks if b[0] < row["after"]]
        elif kind == "weak-namespace":
            if ns_map:
                block(row, "with_weak_namespace requires an explicit scope review")
        elif kind == "open":
            if check_span(row) in removed_opens:
                continue
            names = row["names"]
            written = spelling(row)
            new_names = [opens.get(n, n) for n in names]
            if None in new_names:
                block(row, "obsolete namespace requires a plain top-level open")
                continue
            policy_match = written.removeprefix("_root_.") in opens
            if any(n not in opens and any(under(n, old) for old in migration.namespace_origins)
                   for n in names):
                block(row, "explicit opens policy needed for a renamed namespace")
                continue
            relative_policy = any(old.endswith("." + written.removeprefix("_root_."))
                                  for old in opens)
            if not names and (policy_match or ns_map or relative_policy):
                block(row, "namespace operand could not be resolved")
                continue
            changed_opens.update(n for n, new in zip(names, new_names) if n != new)
            mode = row["mode"]
            plain = mode.removeprefix("local-") in ("simple", "scoped")
            if not plain:
                guard = row["command"]
                if "start" not in guard:
                    block(row, f"missing syntax range for {mode}")
                    continue
                lo, hi = check_span(guard)
                members = [ref for (a, b), candidates in refs.items() if lo <= a and b <= hi
                           for ref in candidates if ref["name"]]
                if new_names != names or any(migration.target(ref) for ref in members):
                    compatible = len(names) == 1 and len(new_names) == 1 and bool(members)
                    if compatible:
                        for ref in members:
                            member = relative(ref["name"], names[0])
                            target = migration.target(ref)
                            actual = target["new"] if target else ref["name"]
                            if not member or actual != new_names[0] + "." + member:
                                compatible = False
                                break
                    if not compatible:
                        block(row, f"{mode} members do not move together with their namespace")
                guarded.append((lo, hi))
            if new_names == names and not ns_map:
                continue
            if len(set(new_names)) != 1 or (mode.startswith("local-") and
                                           written.removeprefix("_root_.") not in names):
                block(row, "ambiguous or relative nested open")
                continue
            edit(row, "_root_." + new_names[0])

    binder_parents = defaultdict(list)
    for candidates in refs.values():
        for ref in candidates:
            if ref["kind"] == "binder" and (target := migration.target(ref)):
                binder_parents[ref["module"]].append(target)

    record_labels = [check_span(r) for r in data["commands"]
                     if r["kind"] == "record-label" and "start" in r]
    for (a, b), candidates in refs.items():
        old_text = source[a:b].decode()
        # A cases/induction alternative names a constructor by its leaf. Lean
        # rejects a fully qualified name there, even when it names that same
        # constructor. Preserve an unchanged short label; term occurrences below
        # still receive their canonical name.
        line_start = source.rfind(b"\n", 0, a) + 1
        short_alternative = ("." not in old_text and
                             re.fullmatch(rb"[ \t]*\|[ \t]+@?", source[line_start:a]) is not None)
        if short_alternative and all(
                (target := migration.target(ref)) is None or
                target["new"].rsplit(".", 1)[-1] == old_text
                for ref in candidates):
            continue
        record_label = any(lo <= a and b <= hi for lo, hi in record_labels)
        replacements = set()
        other_resolution = False
        field_binder = any(ref["kind"] == "binder" and
                           (migration.target(ref) or {}).get("field_namespace")
                           for ref in candidates)
        for ref in candidates:
            # The command elaborator may also record a local at the position
            # of a qualified declaration binder.
            if field_binder and ref["kind"] == "local":
                continue
            row = migration.target(ref)
            old = private_user_name(ref["module"], ref["name"])
            name = row["new"] if row else old
            if record_label:
                if row and (ref["kind"] != "field" or name.rsplit(".", 1)[-1] != old.rsplit(".", 1)[-1]):
                    block(ref, f"structure field label requires review for {old}")
                continue
            if ref["kind"] == "syntax" and old_text.startswith("@") and any(
                    inner["kind"] == "term" and (inner["module"], inner["name"]) == (ref["module"], ref["name"])
                    for inner in refs.get((a + 1, b), ())):
                continue
            curr = ref["namespace"]
            new_curr = rename_prefix(curr, ns_map)
            parents = []
            if new_curr != rename_prefix(curr, {}):
                parts = PARTS.findall(curr)
                parents = [".".join(parts[:i]) for i in range(1, len(parts) + 1)]
            loses_relative_scope = any(old == prefix + "." + old_text for prefix in (*parents, *changed_opens))
            if row is None and ref["kind"] == "field":
                parent_name = old.rpartition(".")[0]
                receiver = (migration.symbols.get((ref["module"], parent_name))
                            or migration.public_symbols.get(parent_name))
                if receiver and receiver["new"] != parent_name:
                    block(ref, f"unmoved extension on renamed receiver requires an explicit call or export for {old}")
                    continue
            if row is None and ref["kind"] in ("term", "syntax"):
                parents = [old.rpartition(".")[0]]
                if old.endswith("_assoc"):
                    parents.append(old[:-6])
                if any((parent := migration.symbols.get((ref["module"], name)))
                       and parent["new"] != name for name in parents):
                    block(ref, f"unmapped member of renamed declaration requires review for {old}")
                    continue
            if row is None and not loses_relative_scope:
                if ref["kind"] in ("local", "term", "field"):
                    other_resolution = True
                continue
            if any(lo <= a and b <= hi for lo, hi in guarded):
                continue
            dotted = source[max(0, a - 1):a] == b"."
            if ref["kind"] == "field" or (dotted and ref["kind"] != "binder"):
                old_parent, _, old_field = old.rpartition(".")
                new_parent, _, new_field = name.rpartition(".")
                parent = (migration.symbols.get((ref["module"], old_parent))
                          or migration.public_symbols.get(old_parent))
                exports_receiver = row is not None and bool(row.get("field_namespace"))
                stays_with_type = parent is not None and parent["new"] == new_parent
                if old_text == old_field and (stays_with_type or exports_receiver):
                    replacements.add(new_field)
                    continue
                block(ref, f"field notation requires checking receiver for {old}")
                continue
            if not IDENT.fullmatch(old_text):
                block(ref, f"non-identifier syntax for {old}")
                continue
            if ref["kind"] == "binder":
                if not row:
                    continue
                normal = old_text.removeprefix("_root_.")
                if normal == old or (row.get("field_namespace") and old.endswith("." + normal)):
                    replacements.add("_root_." + name)
                elif (normal == old.rsplit(".", 1)[-1] and
                      any(old.startswith(parent["old"] + ".") and name.rpartition(".")[0] ==
                          parent["new"] + old.rpartition(".")[0][len(parent["old"]):]
                          for parent in binder_parents.get(ref["module"], ()))):
                    # Constructor and projection binders stay under their moved parent.
                    replacements.add(name.rsplit(".", 1)[-1])
                elif normal == relative(old, rename_prefix(curr, {})):
                    dest = relative(name, new_curr)
                    replacements.add(dest if dest else "_root_." + name)
                else:
                    block(ref, f"declaration binder requires review for {old}")
            elif ref["kind"] == "term":
                literal = old_text.removeprefix("_root_.")
                if "." in literal and literal != old and not old.endswith("." + literal):
                    block(ref, f"dotted term is not a suffix of its resolved name {old}")
                else:
                    replacements.add("_root_." + name)
            else:
                block(ref, f"macro, option, or documentation syntax for {old}")
        if replacements:
            if len(replacements) != 1 or (other_resolution and any(r != old_text for r in replacements)):
                block(candidates[0], "span has more than one elaborated resolution")
            else:
                edit(candidates[0], next(iter(replacements)))

    # Register a new field spelling where the receiver's namespace differs from
    # the method's storage namespace. Lean export adds a name-resolution entry,
    # without adding a second kernel declaration.
    if migration.field_exports.get(module):
        declarations = [r for r in data["commands"]
                        if r["kind"] == "declaration-command" and "start" in r]
        insertions = defaultdict(list)
        for old, target, receiver, leaf in migration.field_exports[module]:
            binders = [r for candidates in refs.values() for r in candidates
                       if r["kind"] == "binder" and r["module"] == module and r["name"] == old]
            ranges = {check_span(r) for r in binders}
            containing = [cmd for cmd in declarations
                          if any(cmd["start"] <= a and b <= cmd["stop"] for a, b in ranges)]
            if len(ranges) != 1 or len(containing) != 1:
                diagnostics.append({"name": old, "reason": "field export requires one positioned declaration"})
                continue
            _, stop = check_span(containing[0])
            insertions[stop].append(f"with_weak_namespace _root_.{receiver} export _root_.{target} ({leaf})")
        for stop, commands in insertions.items():
            edits[stop, stop] = "\n\n" + "\n".join(sorted(commands)) + "\n"

    text = source.decode()
    code = code_only(text)
    for match in IMPORT.finditer(code):
        old = match[1]
        if old in migration.modules:
            a, b = match.span(1)
            edit({"start": len(text[:a].encode()), "stop": len(text[:b].encode())}, migration.modules[old])

    # A qualified name in quoted or custom syntax can lack a semantic reference.
    # Keep such spans for review instead of blindly editing the token.
    raw_ranges = sorted(set(refs) | set(edits))
    ranges = []
    for lo, hi in raw_ranges:
        # A global value and its projection can have separate semantic spans.
        # Bridge only literal dots; an unindexed member still requires review.
        if ranges and (lo <= ranges[-1][1] or
                       source[ranges[-1][1]:lo].strip(b".") == b""):
            ranges[-1] = (ranges[-1][0], max(ranges[-1][1], hi))
        else:
            ranges.append((lo, hi))
    ends = []
    for _, stop in ranges:
        ends.append(max(ends[-1] if ends else 0, stop))
    for token in IDENT.finditer(code):
        literal = token[0].removeprefix("_root_.")
        if (literal not in migration.old_public and
                literal.rpartition(".")[0] not in migration.old_public and
                not (literal.endswith("_assoc") and literal[:-6] in migration.old_public)):
            continue
        a, b = (len(text[:p].encode()) for p in token.span())
        index = bisect_right(ranges, (a, len(source))) - 1
        if index < 0 or ends[index] < b:
            block({"start": a, "stop": b}, "old qualified name has no semantic source span")

    position = 0
    result = bytearray()
    for (a, b), replacement in sorted(edits.items()):
        if a < position:
            block({"start": a, "stop": b}, "overlapping source ranges")
            continue
        result.extend(source[position:a])
        result.extend(replacement.encode())
        position = b
    result.extend(source[position:])
    return (None if diagnostics else bytes(result)), diagnostics


def select_aliases(inputs, migration):
    used = defaultdict(set)
    existing = defaultdict(set)
    for label, path, data in inputs:
        current = data["module"]
        destination = migration.modules.get(current, current)
        if under(current, IC) or under(destination, IC):
            continue
        for ref in data["refs"]:
            if ref["kind"] in ("binder", "local") or ref["name"].startswith("_private."):
                continue
            key = ref["module"], ref["name"]
            if ref["name"] in migration.existing_aliases:
                existing[ref["name"]].add((label, path, ref["start"], ref["stop"]))
            elif key in migration.symbols:
                used[key].add((label, path, ref["start"], ref["stop"]))
    selected = {}
    for key, uses in sorted(used.items()):
        row = migration.symbols[key]
        old = row["old"]
        if old in selected:
            other = selected[old]["module"]
            raise ValueError(f"alias {old} resolves to both {other} and {row['module']}; separate the scopes")
        selected[old] = {**row, "uses": sorted(uses)}
    return selected, {name: sorted(uses) for name, uses in sorted(existing.items())}


def render_aliases(selected, migration, helper, since):
    helper = validate_name(helper)
    if date.fromisoformat(since).isoformat() != since:
        raise ValueError("expected an ISO alias date")
    by_type = {old: sorted(set(row.get("type_dependencies", [])) & selected.keys())
               for old, row in selected.items()}
    order = tuple(TopologicalSorter(by_type).static_order())
    modules = {
        validate_name(row.get("new_module", migration.modules.get(row["module"], row["module"])))
        for row in selected.values()
    }
    lines = ["module", "", f"public meta import {helper}"]
    lines.extend(f"public import {module}" for module in sorted(modules))
    lines.extend(["", "@[expose] public section", ""])
    for old in order:
        lines.extend([f'@[deprecated (since := "{since}")]',
                      f'deprecated_alias _root_.{old} := _root_.{selected[old]["new"]}', ""])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    for name in ("collect", "rewrite", "aliases"):
        cmd = sub.add_parser(name)
        cmd.add_argument("--output", type=Path, required=True, help="new directory for generated artifacts")
        if name == "aliases":
            cmd.add_argument("--scope", nargs=4, action="append", required=True,
                             metavar=("LABEL", "ROOT", "FILES", "INDEX"))
            cmd.add_argument("--helper", required=True, help="post-move DeprecatedAlias module")
            cmd.add_argument("--since", required=True)
        else:
            cmd.add_argument("--root", type=Path, required=True)
            cmd.add_argument("--files", type=Path, required=True, help="JSON array of relative Lean paths")
        if name != "collect":
            cmd.add_argument("--plan", type=Path, required=True)
        if name == "collect":
            cmd.add_argument("--lean", type=Path, help="direct Lean executable instead of lake env lean")
        if name == "rewrite":
            cmd.add_argument("--index", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.action == "collect":
            collect(args.root, file_list(args.files), args.output.resolve(), args.lean)
            return 0
        migration = Migration(read_json(args.plan))
        if args.action == "rewrite":
            args.output.mkdir()
            review, written = {}, set()
            for path, data in captures(args.root, file_list(args.files), args.index):
                preview, issues = rewrite(data, migration)
                if issues:
                    review[path] = issues
                    continue
                dest_module = migration.modules.get(data["module"])
                dest_path = (Path(*[p.removeprefix("«").removesuffix("»") for p in PARTS.findall(dest_module)])
                             if dest_module else None)
                dest = args.output / (dest_path.parent / (dest_path.name + ".lean") if dest_path else path)
                if dest in written:
                    raise ValueError(f"duplicate preview path: {dest}")
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(preview)
                written.add(dest)
            write_json(args.output / "review.json", review)
            return int(bool(review))
        labels = [scope[0] for scope in args.scope]
        if len(set(labels)) != len(labels):
            raise ValueError("scope labels must be distinct")
        inputs = ((label, path, data) for label, root, files, index in args.scope
                  for path, data in captures(Path(root), file_list(Path(files)), Path(index)))
        selected, existing = select_aliases(inputs, migration)
        alias_source = render_aliases(selected, migration, args.helper, args.since)
        args.output.mkdir()
        (args.output / "Aliases.lean").write_text(alias_source)
        scopes = [{"label": label, "files": len(file_list(Path(files)))}
                  for label, _, files, _ in args.scope]
        write_json(args.output / "aliases.json",
                   {"scopes": scopes, "selected": list(selected.values()), "existing": existing})
        return 0
    except (KeyError, ValueError, OSError, CycleError, subprocess.CalledProcessError) as error:
        parser.exit(2, f"{error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
