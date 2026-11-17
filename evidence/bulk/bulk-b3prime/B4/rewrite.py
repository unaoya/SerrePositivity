#!/usr/bin/env python3
"""Preview exact binding rewrites and explicit imports of moved declaration owners.

Uses the unchanged shared collector/rewriter. Never edits the lane's source tree.
A modified original definition which was split into another owner is retained for
manual merge instead of copying an unsplit old source over the new layout.
"""
import argparse
import json
from pathlib import Path
import re
import sys


def insert_imports(source, modules, code_only):
    if not modules:
        return source
    text = source.decode()
    clean = code_only(text)
    first = re.search(r'(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b', clean)
    if first:
        position = first.start()
    else:
        directives = list(re.finditer(r'(?m)^[ \t]*(?:module|prelude)[ \t]*\r?\n', clean))
        position = directives[-1].end() if directives else 0
    public = bool(re.search(r'(?m)^[ \t]*public[ \t]+(?:meta[ \t]+)?import\b', clean))
    prefix = 'public import ' if public else 'import '
    block = ''.join(prefix + name + '\n' for name in sorted(modules))
    return (text[:position] + block + text[position:]).encode()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['tools', 'root', 'files', 'index', 'plan', 'output']:
        p.add_argument('--' + name, type=Path, required=True)
    args = p.parse_args()
    sys.path.insert(0, str(args.tools.resolve()))
    import klw1_namespace as K
    from bulk_namespace import rewrite
    from layer_check import code_only, imports
    migration = K.Migration(K.read_json(args.plan))
    ownership = K.read_json(args.plan.parent / 'declaration-import-owners.json')
    if ownership['unresolved']:
        raise ValueError('import-owner table contains unresolved rows')
    owners = {(row['module'], row['old']): row for row in ownership['rows']}
    if len(owners) != len(ownership['rows']):
        raise ValueError('duplicate import-owner row')
    target_root = args.tools.resolve().parents[1]
    args.output.mkdir()
    review, supplement, written = {}, {}, set()
    for path, data in K.captures(args.root, K.file_list(args.files), args.index):
        legacy_module = 'SerrePositivity.Inputs.Perfectoidization'
        legacy_name = 'SerrePositivity.Inputs.exists_perfectoidization_of_finite'
        legacy_refs = [ref for ref in data['refs'] if ref['name'] == legacy_name and ref['kind'] not in ('binder', 'local')]
        if legacy_module in imports(data['source']) or legacy_refs:
            review[path] = [{'start': ref['start'], 'stop': ref['stop'],
                             'reason': 'deleted wrapper has a different assumption telescope; redirect to the existing BS theorem while retaining the original public definition arguments',
                             'old': legacy_name} for ref in legacy_refs] or [
                {'start': 0, 'stop': len(data['source'].encode()),
                 'reason': 'deleted wrapper import: review the explicit BS import and preserve any original FinitePresentation parameters'}]
            continue
        preview, issues = rewrite(data, migration)
        if issues:
            review[path] = issues
            continue
        current = migration.modules.get(data['module'], data['module'])
        required, bindings, split = set(), set(), []
        for ref in data['refs']:
            if ref['kind'] == 'local' or ref['name'].startswith('_private.'):
                continue
            row = owners.get((ref['module'], ref['name'])) or migration.target(ref)
            if not row:
                continue
            owner = K.validate_name(row.get('new_module', migration.modules.get(row['module'], row['module'])))
            if ref['kind'] == 'binder':
                if ref['module'] == data['module'] and owner != current:
                    split.append({'start': ref['start'], 'stop': ref['stop'],
                                  'reason': 'original definition was split into another owner; merge the local patch into that file',
                                  'old': row['old'], 'new': row['new'], 'new_module': owner})
                continue
            if owner == ref['module'] or owner == current:
                continue
            owner_parts = [s.removeprefix('«').removesuffix('»') for s in K.PARTS.findall(owner)]
            target = target_root / Path(*owner_parts[:-1]) / (owner_parts[-1] + '.lean')
            if not target.is_file():
                raise ValueError(f'{path}: actual moved owner source is missing: {owner}')
            required.add(owner)
            bindings.add((row['module'], row['old'], owner, row['new']))
        if split:
            review[path] = split
            supplement[path] = {'manual_split_definitions': split}
            continue
        if current == 'SerrePositivity.EInfinity' or current.startswith('SerrePositivity.EInfinity.'):
            bs_imports = sorted(m for m in required if m == 'SerrePositivity.BhattScholze' or m.startswith('SerrePositivity.BhattScholze.'))
            if bs_imports:
                review[path] = [{'start': 0, 'stop': len(data['source'].encode()),
                                 'reason': 'moved BS interface use in EInfinity core needs a placement/ownership decision; do not recreate the removed EInfinity-to-BS edge',
                                 'required_bs_modules': bs_imports}]
                continue
        added = required - imports(preview.decode())
        preview = insert_imports(preview, added, code_only)
        assert required <= imports(preview.decode()), path
        dest_module = migration.modules.get(data['module'])
        if dest_module:
            parts = [s.removeprefix('«').removesuffix('»') for s in K.PARTS.findall(dest_module)]
            destination = args.output / Path(*parts[:-1]) / (parts[-1] + '.lean')
        else:
            destination = args.output / path
        if destination in written:
            raise ValueError(f'duplicate preview destination: {destination}')
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(preview)
        written.add(destination)
        supplement[path] = {'added_imports': sorted(added),
                            'moved_binding_owners': [{'old_module': a, 'old': b, 'new_module': c, 'new': d}
                                                    for a, b, c, d in sorted(bindings)]}
    K.write_json(args.output / 'review.json', review)
    K.write_json(args.output / 'imports.json', supplement)
    print(json.dumps({'files_written': len(written), 'blocked_files': len(review),
                      'imports_added': sum(len(r.get('added_imports', [])) for r in supplement.values())}))
    return int(bool(review))


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, OSError, KeyError) as exc:
        sys.exit(str(exc))
