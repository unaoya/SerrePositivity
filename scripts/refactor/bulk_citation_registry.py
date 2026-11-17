#!/usr/bin/env python3
"""Check or regenerate CitationRegistry.lean's registry from research/bibliography.json.
Only the marked registry block is generated; --check is read-only.
"""
import argparse
import json
from pathlib import Path
import re


def block(registry):
    refs = sorted(registry['references'], key=lambda r: r['key'])
    keys = [r['key'] for r in refs]
    if len(set(keys)) != len(keys) or any(not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', k) for k in keys):
        raise ValueError('Citation keys must be distinct simple Lean identifiers')
    if any(not r['edition'].strip() for r in refs):
        raise ValueError('Every reference needs an edition')
    quote = lambda s: json.dumps(s, ensure_ascii=False)
    lines = ['-- BEGIN GENERATED REGISTRY', 'private def knownKeys : List String := [']
    lines += ['  ' + quote(k) + (']' if i == len(keys)-1 else ',') for i, k in enumerate(keys)]
    lines += ['', 'private def knownEditions : List (String × String) := [']
    lines += ['  (' + quote(r['key']) + ', ' + quote(r['edition']) + ')' +
              (']' if i == len(refs)-1 else ',') for i, r in enumerate(refs)]
    lines += ['-- END GENERATED REGISTRY']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    args = parser.parse_args()
    registry = json.loads((args.root / 'research/bibliography.json').read_text())
    path = args.root / 'SerrePositivity/Util/CitationRegistry.lean'
    source = path.read_text()
    generated = block(registry)
    pattern = r'-- BEGIN GENERATED REGISTRY\n.*?-- END GENERATED REGISTRY'
    if len(re.findall(pattern, source, re.S)) != 1:
        parser.error('Expected one marked registry block')
    updated = re.sub(pattern, lambda _: generated, source, flags=re.S)
    if args.write:
        path.write_text(updated)
    elif updated != source:
        parser.exit(1, 'Citation registry is out of date; run with --write\n')
    print(f'Registry matches: {len(registry["references"])} keys')


if __name__ == '__main__':
    main()
