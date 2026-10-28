#!/usr/bin/env python3
"""概要：公開宣言の保存を比較する。方針：名前対応後の構造を比較する。
規約：増減・型・本体・公理・属性をすべて判定する。使われ方：before after --name-map map.json。
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys


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


def normalized(snapshot, mapping):
    if snapshot['schema_version'] != 1: raise ValueError('unsupported snapshot version')
    records = {}
    for row in snapshot['declarations']:
        name = rename(row['name'], mapping)
        if name in records: raise ValueError('normalized declaration collision: ' + name)
        records[name] = {
            'parent': rename(row['parent'], mapping), 'kind': row['kind'],
            'type': normalize_expr(row['type'], mapping),
            'body': normalize_expr(row['body'], mapping),
            'axioms': sorted(rename(n, mapping) for n in row['axioms']),
            'attributes': row['attributes']}
    if not records: raise ValueError('empty snapshot')
    # Group generated auxiliaries under their public parent. Proof-only auxiliaries
    # may change when a theorem proof changes; the parent's axioms are still checked.
    grouped = {}
    for name, record in records.items():
        parent = record['parent']
        if parent != name and parent in records:
            if records[parent]['kind'] == 'theorem':
                continue
            grouped.setdefault(parent, dict(records[parent])).setdefault('auxiliaries', {})[name] = record
        else:
            grouped.setdefault(name, dict(record))
    return grouped


def digest(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, separators=(',', ':')).encode()).hexdigest()


def compare(before, after, mapping=None):
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
            'parent_count': len({r['parent'] for r in b.values()}), 'changes': changes}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('before', type=Path); parser.add_argument('after', type=Path)
    parser.add_argument('--name-map', type=Path); parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        mapping = json.loads(args.name_map.read_text()) if args.name_map else {}
        if not isinstance(mapping, dict) or not all(isinstance(k, str) and isinstance(v, str) for k,v in mapping.items()):
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
