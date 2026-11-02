#!/usr/bin/env python3
"""DG D5. Inventory old module-doc links by default. Apply one document to merged targets."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_source import read_source, write_source

ROOT = Path(__file__).resolve().parents[3]
NAMES = {
    'inventory': 'dg-theory-u12e-general-inventory.md',
    'status': 'dg-theory-m5-status.md',
}
ACTIVE = Path('SerrePositivity/DifferentialGraded')
ARCHIVE = Path('SerrePositivity/Archive/DifferentialGraded')
TOKEN = re.compile(r"""--|/-|(?<![\w'])r(?P<hashes>\#*)"|"|'(?:\\.|[^'\\\n])'""")


def module_docs(text):
    """Like R79, accept only outer /-! blocks, including all such blocks after a merge."""
    spans = []
    pos = 0
    while match := TOKEN.search(text, pos):
        start, pos = match.span()
        token = match[0]
        if token == '--':
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end + 1
        elif token == '/-':
            depth = 1
            for marker in re.finditer(r'/-|-/', text[pos:]):
                depth += 1 if marker[0] == '/-' else -1
                if depth == 0:
                    pos += marker.end()
                    break
            if depth:
                raise ValueError('unterminated block comment')
            if text.startswith('/-!', start):
                spans.append((start, pos))
        elif match['hashes'] is not None:
            close = '"' + match['hashes']
            end = text.find(close, pos)
            if end < 0:
                raise ValueError('unterminated raw string')
            pos = end + len(close)
        elif token == '"':
            end = re.compile(r'(?:[^"\\]|\\.)*"', re.S).match(text, pos)
            if not end:
                raise ValueError('unterminated string')
            pos = end.end()
    return spans


def rewrite(text, document):
    names = NAMES.values() if document == 'all' else [NAMES[document]]
    pattern = re.compile(r'formalization-plans/(?P<name>' + '|'.join(map(re.escape, names)) + r')(?![A-Za-z0-9_.-])')
    matches = list(pattern.finditer(text))
    if not matches:
        return text, Counter()
    docs = module_docs(text)
    for match in matches:
        if not any(a <= match.start() and match.end() <= b for a, b in docs):
            line = text.count('\n', 0, match.start()) + 1
            raise ValueError(f'line {line}: reference outside module docstring')
    return pattern.sub(r'formalization-plans/archive/\g<name>', text), Counter(m['name'] for m in matches)


def files(root, plan):
    if plan is None:
        return sorted(p for area in (ACTIVE, ARCHIVE) for p in (root / area).rglob('*.lean'))
    rows = json.loads(plan.read_text())
    targets = []
    for row in rows:
        if row['action'] != 'merge':
            continue
        name = row['module']
        if not re.fullmatch(r'SerrePositivity\.DifferentialGraded(?:\.\w+)+', name):
            raise ValueError(f'not a DG merge target: {name}')
        path = root / (name.replace('.', '/') + '.lean')
        if not path.is_file():
            raise ValueError(f'merge target missing: {name}')
        targets.append(path)
    if not targets:
        raise ValueError('no DG merge targets')
    return sorted(set(targets))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--plan', type=Path, help='restrict to existing merge destinations in a DG plan')
    parser.add_argument('--document', choices=['all', *NAMES], default='all')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--dry-run', action='store_true')
    args = parser.parse_args()
    if args.apply and (args.plan is None or args.document == 'all'):
        parser.error('--apply requires --plan and a single --document')
    root = args.root.resolve()
    if args.apply and not (root / 'formalization-plans/archive' / NAMES[args.document]).is_file():
        parser.error('archive document must be in place before --apply')
    changes = {}
    hits, affected = Counter(), Counter()
    for path in files(root, args.plan):
        before = read_source(path)
        try:
            after, counts = rewrite(before, args.document)
        except ValueError as exc:
            raise ValueError(f'{path.relative_to(root)}: {exc}') from exc
        if counts:
            area = 'archive' if path.is_relative_to(root / ARCHIVE) else 'active'
            changes[path] = (before, after)
            for name, count in counts.items():
                hits[area, name] += count
                affected[area, name] += 1
    if args.apply:
        for path, (before, _) in changes.items():
            if read_source(path) != before:
                raise ValueError(f'source changed since scan: {path}')
        for path, (_, after) in changes.items():
            write_source(path, after)
    print('APPLIED' if args.apply else 'DRY RUN', f'{len(changes)} files')
    for area in ('active', 'archive'):
        for key, name in NAMES.items():
            if args.document in ('all', key):
                print(f'{area} {name}: {affected[area, name]} files, {hits[area, name]} references')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError) as exc:
        sys.exit(f'rewrite_dg_docs: STOP: {exc}')
