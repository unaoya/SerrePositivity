#!/usr/bin/env python3
"""Validate or replay the reviewed B2 edit bundle on an isolated worktree.
The default is read-only. All source hashes and destinations are checked before
--apply writes a file. B2 uses --check-against to compare every generated output
with the built preview; a new main snapshot requires a refreshed bundle.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_path(root, relative):
    path = Path(relative)
    if path.is_absolute() or '..' in path.parts:
        raise ValueError(f'Unsafe relative path: {relative}')
    full = root / path
    if not full.resolve().is_relative_to(root):
        raise ValueError(f'Path leaves the worktree through a symlink: {relative}')
    return full


def load_bundle(path):
    with gzip.open(path, 'rt') as stream:
        bundle = json.load(stream)
    if bundle['schema_version'] != 1:
        raise ValueError('Unsupported bundle version')
    targets = [r['target'] for r in bundle['outputs']]
    if len(targets) != len(set(targets)):
        raise ValueError('Duplicate output destination')
    if set(targets) & set(bundle['deletions']):
        raise ValueError('An output destination is also deleted')
    return bundle


def replay(source, edits):
    previous = 0
    for edit in edits:
        start, stop = edit['start'], edit['stop']
        if not previous <= start <= stop <= len(source):
            raise ValueError('Invalid or overlapping byte edits')
        previous = stop
    result = source
    for edit in reversed(edits):
        result = result[:edit['start']] + edit['text'].encode() + result[edit['stop']:]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--bundle', type=Path, required=True)
    parser.add_argument('--check-against', type=Path)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    root = args.root.resolve()
    bundle = load_bundle(args.bundle)
    # An approval for a freeze is separate from B2 preparation. This tool is
    # deliberately never used to mutate the coordinator's main worktree.
    if args.apply:
        branch = subprocess.check_output(
            ['git', 'branch', '--show-current'], cwd=root, text=True).strip()
        if branch == 'main':
            raise ValueError('Apply on the dedicated refactor worktree, then merge through the coordinator')
    if expected_library := bundle.get('library_sha256'):
        library = safe_path(root, 'SerrePositivity/Util/Citation.lean')
        if not library.exists() or digest(library.read_bytes()) != expected_library:
            raise ValueError('Citation implementation differs from the reviewed preview')
    source_bytes = {}
    for relative, expected in bundle['sources'].items():
        data = safe_path(root, relative).read_bytes()
        if digest(data) != expected:
            raise ValueError(f'Source changed since the reviewed preview: {relative}')
        source_bytes[relative] = data
    for relative in bundle['deletions']:
        safe_path(root, relative)
        if relative not in source_bytes:
            raise ValueError(f'Deletion lacks an original source receipt: {relative}')
    outputs = {}
    for row in bundle['outputs']:
        source = source_bytes[row['source']] if row['source'] else b''
        result = replay(source, row['edits'])
        if digest(result) != row['sha256']:
            raise ValueError(f'Output hash mismatch: {row["target"]}')
        target = safe_path(root, row['target'])
        if target.exists() and row['target'] not in source_bytes:
            if digest(target.read_bytes()) != row['sha256']:
                raise ValueError(f'Destination collision: {row["target"]}')
        temporary = target.with_name(target.name + '.bulk-preview-tmp')
        if args.apply and (temporary.exists() or temporary.is_symlink()):
            raise ValueError(f'Temporary destination already exists: {temporary}')
        outputs[row['target']] = result
    if args.check_against:
        preview = args.check_against.resolve()
        for relative, data in outputs.items():
            if safe_path(preview, relative).read_bytes() != data:
                raise ValueError(f'Preview differs from the bundle: {relative}')
        for relative in bundle['deletions']:
            if safe_path(preview, relative).exists():
                raise ValueError(f'Deleted source remains in preview: {relative}')
    if args.apply:
        # Every original was read and validated above, including a source whose
        # old path will become a compatibility shim. Never read a moved source.
        for relative, data in outputs.items():
            path = safe_path(root, relative)
            path.parent.mkdir(parents=True, exist_ok=True)
            temporary = path.with_name(path.name + '.bulk-preview-tmp')
            if temporary.exists() or temporary.is_symlink():
                raise ValueError(f'Temporary destination already exists: {temporary}')
            temporary.write_bytes(data)
            temporary.replace(path)
        for relative in bundle['deletions']:
            safe_path(root, relative).unlink()
    print(json.dumps({'status': 'applied' if args.apply else 'checked',
                      'sources': len(source_bytes), 'outputs': len(outputs),
                      'deletions': len(bundle['deletions']),
                      'matches_preview': bool(args.check_against)}))


if __name__ == '__main__':
    main()
