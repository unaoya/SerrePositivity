#!/usr/bin/env python3
"""概要：公開宣言の保存を比較する。方針：名前正規化後の構造またはそのハッシュを比較する。
規約：増減・型・本体・公理・属性をすべて判定する。使われ方：before after --name-map map.json。
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import sys
from lean_source import transient_names, parse_source, declaration_owner, Unsupported


def rename(name, mapping):
    for old in sorted(mapping, key=len, reverse=True):
        if name == old or name.startswith(old + '.'):
            return mapping[old] + name[len(old):]
    return name


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


def normalized(snapshot, mapping, use_hash=False, module_map=None):
    if snapshot['schema_version'] not in (1, 2):
        raise ValueError('unsupported snapshot version')
    module_map = module_map or {}
    records = {}
    skipped = set()
    sources = {s['module']: s for s in snapshot.get('sources', [])}
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
            if row['name'] in transient:
                continue
            parent = declaration_owner(row, names, by_name) if names else None
            parent = parent or row['parent']
            target = split.get(row['name'], split.get(parent, module_map.get('modules', {}).get(module, module)))
            key = (rename(row['name'], mapping), target)
            if key in records:
                raise ValueError('normalized declaration collision: ' + repr(key))
            records[key] = {
                'parent': rename(parent, mapping), 'kind': row['kind'],
                'type': expression_value(row, 'type', mapping, use_hash),
                'body': expression_value(row, 'body', mapping, use_hash),
                'axioms': sorted(rename(n, mapping) for n in row['axioms']),
                'attributes': row['attributes']}
    # Group generated auxiliaries under their public parent. Proof-only auxiliaries
    # may change when a theorem proof changes; the parent's axioms are still checked.
    grouped = {}
    for name, record in records.items():
        parent = (record['parent'], name[1])
        if parent != name and parent in records:
            if records[parent]['kind'] == 'theorem' and re.search(r'\._proof_\d', name[0]):
                continue
            grouped.setdefault(parent, dict(records[parent])).setdefault('auxiliaries', {})[name[0]] = record
        else:
            grouped.setdefault(name, dict(record))
    return grouped, sorted(skipped)


def digest(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, separators=(',', ':')).encode()).hexdigest()


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
    return {'status': 'FAIL' if changes else 'PASS', 'before_count': len(a), 'after_count': len(b),
            'parent_count': len({(r['parent'], key[1]) for key, r in b.items()}), 'changes': changes,
            'transient': {'before': skipped_a, 'after': skipped_b}}


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
