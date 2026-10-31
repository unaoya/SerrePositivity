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


def normalized(snapshot, mapping, use_hash=False):
    if snapshot['schema_version'] not in (1, 2):
        raise ValueError('unsupported snapshot version')
    records = {}
    transient = set(transient_names(snapshot))
    source_names = {}
    for source in snapshot.get('sources', []):
        try: source_names[source['module']] = set(parse_source(source['source'], snapshot=snapshot, module=source['module']).declarations)
        except Unsupported: pass
    by_name = {r['name']: r for r in snapshot['declarations']}
    for row in snapshot['declarations']:
        if row['name'] in transient: continue
        name = rename(row['name'], mapping)
        if name in records: raise ValueError('normalized declaration collision: ' + name)
        parent = row['parent']
        if row.get('module') in source_names:
            parent = declaration_owner(row, source_names[row['module']], by_name) or parent
        records[name] = {
            'parent': rename(parent, mapping), 'kind': row['kind'],
            'type': expression_value(row, 'type', mapping, use_hash),
            'body': expression_value(row, 'body', mapping, use_hash),
            'axioms': sorted(rename(n, mapping) for n in row['axioms']),
            'attributes': row['attributes']}
    # Group generated auxiliaries under their public parent. Proof-only auxiliaries
    # may change when a theorem proof changes; the parent's axioms are still checked.
    grouped = {}
    for name, record in records.items():
        parent = record['parent']
        if parent != name and parent in records:
            if records[parent]['kind'] == 'theorem' and re.search(r'\._proof_\d', name):
                continue
            grouped.setdefault(parent, dict(records[parent])).setdefault('auxiliaries', {})[name] = record
        else:
            grouped.setdefault(name, dict(record))
    return grouped


def digest(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, separators=(',', ':')).encode()).hexdigest()


def compare(before, after, mapping=None):
    hashed = [snap for snap in (before, after) if snap['schema_version'] == 2]
    if hashed:
        if len(hashed) != 2:
            raise ValueError('full-structure and hash snapshots use different algorithms; recapture both sides')
        rules = hashed[0]['name_map']
        if any(snap['name_map'] != rules or snap['hash_algorithm'] != hashed[0]['hash_algorithm']
               for snap in hashed) or (mapping is not None and mapping != rules):
            raise ValueError('snapshot name maps or hash algorithms differ; recapture with the same settings')
        a = normalized(before, rules, use_hash=True)
        b = normalized(after, rules, use_hash=True)
    else:
        a, b = normalized(before, mapping or {}), normalized(after, {})
    changes = []
    for name in sorted(a.keys() - b.keys()): changes.append({'name': name, 'change': 'removed'})
    for name in sorted(b.keys() - a.keys()): changes.append({'name': name, 'change': 'added'})
    for name in sorted(a.keys() & b.keys()):
        for field in sorted(a[name].keys() | b[name].keys()):
            if a[name].get(field) != b[name].get(field):
                changes.append({'name': name, 'parent': b[name]['parent'], 'change': field,
                                'before_sha256': digest(a[name].get(field)), 'after_sha256': digest(b[name].get(field))})
    return {'status': 'FAIL' if changes else 'PASS', 'before_count': len(a), 'after_count': len(b),
            'parent_count': len({r['parent'] for r in b.values()}), 'changes': changes,
            'transient': {'before': transient_names(before), 'after': transient_names(after)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('before', type=Path); parser.add_argument('after', type=Path)
    parser.add_argument('--name-map', type=Path); parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        mapping = json.loads(args.name_map.read_text()) if args.name_map else None
        if args.name_map and (not isinstance(mapping, dict) or not all(isinstance(k, str) and isinstance(v, str) for k,v in mapping.items())):
            raise ValueError('name map must be an object of old names to new names')
        result = compare(json.loads(args.before.read_text()), json.loads(args.after.read_text()), mapping)
        rendered = json.dumps(result, ensure_ascii=False, indent=2) + '\n'
        print(rendered, end='')
        if args.output: args.output.write_text(rendered)
        return int(result['status'] == 'FAIL')
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('compare_snapshots: error: ' + str(exc), file=sys.stderr); return 2


if __name__ == '__main__':
    sys.exit(main())
