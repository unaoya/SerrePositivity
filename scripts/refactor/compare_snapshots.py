#!/usr/bin/env python3
"""概要：公開宣言の保存を比較する。方針：名前正規化後の構造またはそのハッシュを比較する。
規約：増減・型・本体・公理・属性をすべて判定する。使われ方：before after --name-map map.json。
"""
import argparse
from collections import ChainMap
import hashlib
import json
import re
from pathlib import Path
import sys
from layer_check import code_only
from lean_source import transient_names, parse_source, declaration_owner, Unsupported
from snapshot_identity import notation_auxiliary


def rename(name, mapping):
    prefix = name
    while True:
        if prefix in mapping:
            return mapping[prefix] + name[len(prefix):]
        prefix, separator, _ = prefix.rpartition('.')
        if not separator:
            return name



def normalize_generated_name(name, modules):
    """Map module spellings embedded in Lean macro/unexpander auxiliary names.

    Match a complete encoded module and generated-name marker, never an ordinary
    identifier substring. The private macro suffix embeds the same module again.
    Hashes remain unchanged: renamed rows must still pass every field comparison.
    """
    match = re.search(r'(^|\.)_aux_(.*?)___(?=macroRules_|unexpand_)', name)
    if match is None:
        return name
    encoded_old = match[2]
    destinations = {old.replace('.', '_'): new.replace('.', '_')
                    for old, new in modules.items()}
    if encoded_old not in destinations:
        return name
    encoded_new = destinations[encoded_old]
    name = name[:match.start(2)] + encoded_new + name[match.end(2):]
    return re.sub(r'_private_' + re.escape(encoded_old) + r'_(?=\d+_)',
                  lambda _: '_private_' + encoded_new + '_', name)


def normalize_expr(value, mapping):
    if not isinstance(value, list): return value
    result = [normalize_expr(v, mapping) for v in value]
    if value and value[0] in ('const', 'proj', 'fvar', 'mvar', 'param', 'level-mvar'):
        result[1] = rename(value[1], mapping)
    return result


def expression_value(row, field, mapping, use_hash):
    if not use_hash and field in row:
        return normalize_expr(row[field], mapping)
    if field in row and mapping and normalize_expr(row[field], mapping) != row[field]:
        raise ValueError('legacy expression requires a fresh snapshot with the same --name-map')
    value = row[field + '_hash']
    if not isinstance(value, str) and not (field == 'body' and value is None):
        raise ValueError('invalid ' + field + '_hash for ' + row['name'])
    return value


def declaration_source(source):
    """Project resolution exports and alias declarations onto the source parser's syntax."""
    qual = r"\w[\w'.]*"
    command = re.compile(rf"(?m)^with_weak_namespace _root_\.{qual} export _root_\.{qual} \(\w[\w']*\)[ \t]*$")
    alias = re.compile(r"(?m)^(?:(?:noncomputable|unsafe|meta|private|public|protected)[ \t]+)*"
                       r"(deprecated_alias)(?=[ \t]+\S+[ \t]*:=)")
    mask = code_only(source)
    edits = [(match.start(), match.end(), "") for match in command.finditer(mask)]
    edits.extend((*match.span(1), "def") for match in alias.finditer(mask))
    for start, end, replacement in sorted(edits, reverse=True):
        source = source[:start] + replacement.ljust(end - start) + source[end:]
    return source


def normalized(snapshot, mapping, use_hash=False, module_map=None, report_proof_parents=None):
    if snapshot['schema_version'] not in (1, 2):
        raise ValueError('unsupported snapshot version')
    module_map = module_map or {}
    moved_modules = module_map.get('modules', {})
    records = {}
    reference_kinds = {}
    report_proof_parents = report_proof_parents or set()
    proof_irrelevant = snapshot.get("proof_irrelevant", False)
    skipped = set()
    sources = {s['module']: {**s, 'source': declaration_source(s['source'])}
               for s in snapshot.get('sources', [])}
    by_module = {}
    for row in snapshot['declarations']:
        by_module.setdefault(row.get('module', ''), []).append(row)
    overrides = snapshot.get('transient_rows')
    known = {(r['name'], r['module']) for r in overrides or []}
    for module, rows in by_module.items():
        local = {'sources': [sources[module]] if module in sources else [], 'declarations': rows}
        transient = ({r['name'] for r in rows if (r['name'], module) in known}
                     if overrides is not None else set(transient_names(local)))
        skipped.update(transient)
        by_name = {r['name']: r for r in rows}
        names = set()
        if module in sources:
            try:
                names = set(parse_source(sources[module]['source'], snapshot=local, module=module).declarations)
            except Unsupported:
                pass
        split = module_map.get('declarations', {}).get(module, {})
        for row in rows:
            if row['name'] in transient or notation_auxiliary(row['name'], module, names):
                skipped.add(row['name'])
                continue
            parent = declaration_owner(row, names, by_name) if names else None
            parent = parent or row['parent']
            target = split.get(row['name'], split.get(parent, moved_modules.get(module, module)))
            generated_modules = ChainMap({module: target}, moved_modules)
            def normalized_name(name):
                return normalize_generated_name(rename(name, mapping), generated_modules)
            key = (normalized_name(row['name']), target)
            if key in records:
                raise ValueError('normalized declaration collision: ' + repr(key))
            reference_kinds[key] = row.get('reference_kind', 'named')
            records[key] = {
                'parent': normalized_name(parent), 'kind': row['kind'],
                'type': expression_value(row, 'type', mapping, use_hash),
                'body': expression_value(row, 'body', mapping, use_hash),
                'axioms': sorted(normalized_name(n) for n in row['axioms']),
                'attributes': row['attributes']}
    # Group generated auxiliaries under their public parent. Proof-only auxiliaries
    # may change when a theorem proof changes; the parent's axioms are still checked.
    grouped = {}
    for name, record in records.items():
        parent = (record['parent'], name[1])
        if parent != name and parent in records:
            proof_parent = records[parent]['kind'] == 'theorem' or (
                proof_irrelevant and records[parent]['kind'] in ('def', 'abbrev', 'instance'))
            if proof_parent and re.search(r'\._proof_\d+(?:$|\.)', name[0]):
                # The proof marker removes this helper from a matching parent's
                # meaning. If that parent's type/body differs, retain the helper
                # as its own row so the report shows both differences.
                if parent in report_proof_parents:
                    grouped[name] = dict(record)
                continue
            if proof_irrelevant and reference_kinds[name] in ('proof', 'generated'):
                # These helper references are already expanded by the parent's
                # type/body fingerprints. Comparing a second inventory here
                # would make Lean's cross-declaration sharing observable again.
                # Keep their actual names in auxiliary_groups(), outside equality.
                continue
            if proof_irrelevant:
                value = {k: v for k, v in record.items() if k != 'parent'}
                group = grouped.setdefault(parent, dict(records[parent])).setdefault('auxiliaries', {})
                group[digest(value)] = value  # structural set, not generated names/multiplicity
            else:
                grouped.setdefault(parent, dict(records[parent])).setdefault('auxiliaries', {})[name[0]] = record
        else:
            grouped.setdefault(name, dict(record))
    return grouped, sorted(skipped)


def digest(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, separators=(',', ':')).encode()).hexdigest()



def auxiliary_groups(snapshot, mapping=None, module_map=None):
    """Audit trail only: references are compared in their parent's DAG hash.

    Explicit source declarations are never classified from a generated-looking
    spelling alone. Keep actual names for review, but use parent/module identity
    as the group key, just as for declaration comparison and transient ownership.
    """
    mapping, module_map = mapping or {}, module_map or {}
    sources = {s['module']: declaration_source(s['source']) for s in snapshot.get('sources', [])}
    by_module = {}
    for row in snapshot['declarations']:
        by_module.setdefault(row.get('module', ''), []).append(row)
    result = {}
    for module, local in by_module.items():
        by_name = {r['name']: r for r in local}
        names = set()
        if module in sources:
            try:
                names = set(parse_source(sources[module], snapshot={'declarations': local}, module=module).declarations)
            except Unsupported:
                pass
        for row in local:
            parent = (declaration_owner(row, names, by_name) if names else None) or row['parent']
            if parent == row['name']:
                continue
            split = module_map.get('declarations', {}).get(module, {})
            target = split.get(parent, module_map.get('modules', {}).get(module, module))
            key = (rename(parent, mapping), target)
            result.setdefault(key, set()).add(row['name'])
    return [{'parent': p, 'module': m, 'names': sorted(names)}
            for (p, m), names in sorted(result.items())]


def compare(before, after, mapping=None, module_map=None):
    hashed = [snap for snap in (before, after) if snap['schema_version'] == 2]
    if hashed:
        if len(hashed) != 2:
            raise ValueError('full-structure and hash snapshots use different algorithms; recapture both sides')
        rules = hashed[0]['name_map']
        if any(snap['name_map'] != rules or snap['hash_algorithm'] != hashed[0]['hash_algorithm']
               for snap in hashed) or (mapping is not None and mapping != rules):
            raise ValueError('snapshot name maps or hash algorithms differ; recapture with the same settings')
        a, skipped_a = normalized(before, rules, use_hash=True, module_map=module_map)
        b, skipped_b = normalized(after, rules, use_hash=True)
    else:
        a, skipped_a = normalized(before, mapping or {}, module_map=module_map)
        b, skipped_b = normalized(after, {})
    changed_parents = {
        key for key in a.keys() | b.keys()
        if key not in a or key not in b or any(
            a[key].get(field) != b[key].get(field) for field in ('type', 'body'))}
    if changed_parents:
        a, skipped_a = normalized(before, rules if hashed else mapping or {},
                                  use_hash=bool(hashed), module_map=module_map,
                                  report_proof_parents=changed_parents)
        b, skipped_b = normalized(after, rules if hashed else {},
                                  use_hash=bool(hashed), report_proof_parents=changed_parents)
    def identity(key):
        return {'name': key[0], **({'module': key[1]} if key[1] else {})}
    changes = []
    for name in sorted(a.keys() - b.keys()): changes.append({**identity(name), 'change': 'removed'})
    for name in sorted(b.keys() - a.keys()): changes.append({**identity(name), 'change': 'added'})
    for name in sorted(a.keys() & b.keys()):
        for field in sorted(a[name].keys() | b[name].keys()):
            if a[name].get(field) != b[name].get(field):
                changes.append({**identity(name), 'parent': b[name]['parent'], 'change': field,
                                'before_sha256': digest(a[name].get(field)), 'after_sha256': digest(b[name].get(field))})
    result = {'status': 'FAIL' if changes else 'PASS', 'before_count': len(a), 'after_count': len(b),
            'parent_count': len({(r['parent'], key[1]) for key, r in b.items()}), 'changes': changes,
            'transient': {'before': skipped_a, 'after': skipped_b}}
    if before.get('proof_irrelevant') or after.get('proof_irrelevant'):
        result['auxiliary_groups'] = {
            'before': auxiliary_groups(before, mapping or before.get('name_map'), module_map),
            'after': auxiliary_groups(after, after.get('name_map'))}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('before', type=Path); parser.add_argument('after', type=Path)
    parser.add_argument('--name-map', type=Path); parser.add_argument('--output', type=Path)
    parser.add_argument('--module-map', type=Path, help='before to after: modules and per-module declarations')
    args = parser.parse_args()
    try:
        mapping = json.loads(args.name_map.read_text()) if args.name_map else None
        if args.name_map and (not isinstance(mapping, dict) or not all(isinstance(k, str) and isinstance(v, str) for k,v in mapping.items())):
            raise ValueError('name map must be an object of old names to new names')
        result = compare(json.loads(args.before.read_text()), json.loads(args.after.read_text()), mapping,
                         json.loads(args.module_map.read_text()) if args.module_map else None)
        rendered = json.dumps(result, ensure_ascii=False, indent=2) + '\n'
        print(rendered, end='')
        if args.output: args.output.write_text(rendered)
        return int(result['status'] == 'FAIL')
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('compare_snapshots: error: ' + str(exc), file=sys.stderr); return 2


if __name__ == '__main__':
    sys.exit(main())
