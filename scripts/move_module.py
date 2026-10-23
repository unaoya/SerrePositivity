#!/usr/bin/env python3
"""Move Lean modules and rewrite project imports/references in one reviewed batch.

Dry run is the default. A JSON plan has object maps `moves`, `redirects`, and
`symbols`, plus optional per-file `imports` edits and `file_symbols` overrides. Names are dotted Lean names. `moves` uses git mv; `redirects` removes
an obsolete tracked module and points its imports to an existing canonical one.
`symbols` rewrites qualified-name prefixes (including projections) outside
comments/string literals.
Example: python3 scripts/move_module.py /tmp/moves.json --apply
An imports edit is {"SerrePositivity/F1.lean": {"add": ["SerrePositivity.B"],
"remove": ["SerrePositivity.A"]}}. Additions are public imports in module files, ordinary imports otherwise. Moving a module
does not automatically rename its declarations or its child modules.
`file_symbols` maps source-file paths (before moving) to symbol maps which
replace the corresponding global `symbols` entries in that file. For example,
use an unqualified new name at its definition, and qualified names in callers.
Use --apply after reviewing the printed file list. Files unrelated to the plan
are left alone. This tool never commits or builds.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

NAME = re.compile(r"[A-Za-z_\u0080-\uffff][\w']*(?:\.[A-Za-z_\u0080-\uffff][\w']*)*\Z")
TOKEN = re.compile(r"[\w']+(?:\.[\w']+)*")
IMPORT = re.compile(r"^(\s*(?:public\s+)?import\s+)([\w.']+)(.*)$")


def code_mask(source):
    """Mask comments and strings, preserving offsets and line breaks."""
    out = list(source)
    i = depth = 0
    quoted = False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == '/-':
                out[i:i + 2] = '  '; depth += 1; i += 2
            elif pair == '-/':
                out[i:i + 2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n': out[i] = ' '
                i += 1
        elif quoted:
            ch = source[i]
            if ch != '\n': out[i] = ' '
            i += 1
            if ch == '\\' and i < len(source):
                if source[i] != '\n': out[i] = ' '
                i += 1
            elif ch == '"': quoted = False
        elif pair == '/-':
            out[i:i + 2] = '  '; depth = 1; i += 2
        elif pair == '--':
            while i < len(source) and source[i] != '\n':
                out[i] = ' '; i += 1
        elif source[i] == '"':
            out[i] = ' '; quoted = True; i += 1
        else: i += 1
    return ''.join(out)


def renamed(token, mapping):
    """Longest dotted prefix lookup, independent of the batch's map size."""
    prefix = token
    while prefix:
        if prefix in mapping: return mapping[prefix] + token[len(prefix):]
        prefix = prefix.rpartition('.')[0]
    return None


def rewrite(source, modules, symbols):
    """Rewrite exact import names and explicit symbol prefixes, once each."""
    if not modules and not symbols: return source
    edits = []
    mask = code_mask(source)
    offset = 0
    for line in mask.splitlines(keepends=True):
        is_import = IMPORT.match(line) is not None
        for m in TOKEN.finditer(line):
            token = m[0]
            # Moving A.lean does not move its independently named A.Child
            # module, or change any declaration namespace. Symbols are an
            # explicit separate map; their projections follow the new name.
            replacement = modules.get(token) if is_import else renamed(token, symbols)
            if replacement is not None and replacement != token:
                edits.append((offset + m.start(), offset + m.end(), replacement))
        offset += len(line)
    if not edits: return source
    for a, b, replacement in reversed(edits): source = source[:a] + replacement + source[b:]
    # Imports converging on the same canonical module are deduplicated only
    # when the complete line is identical, so public/private intent is retained.
    seen = set(); lines = []; canonical_modules = set(modules.values())
    mask_lines = code_mask(source).splitlines(keepends=True)
    for line, masked in zip(source.splitlines(keepends=True), mask_lines):
        imported = IMPORT.match(masked)
        if imported and imported[2] in canonical_modules:
            if line in seen: continue
            seen.add(line)
        lines.append(line)
    return ''.join(lines)


def module_path(root, name):
    if not isinstance(name, str) or not NAME.fullmatch(name):
        raise ValueError(f'invalid module name: {name!r}')
    if not name.startswith('SerrePositivity.'):
        raise ValueError(f'expected a project module: {name}')
    return root / (name.replace('.', '/') + '.lean')


def source_path(root, rel):
    """Require canonical repository-relative paths for per-file rules."""
    if not isinstance(rel, str) or Path(rel).is_absolute() or Path(rel).as_posix() != rel or '..' in Path(rel).parts:
        raise ValueError(f'expected a repository-relative source path: {rel!r}')
    src = root / rel
    if not src.resolve().is_relative_to(root) or src.suffix != '.lean' or not src.is_file():
        raise ValueError(f'expected an existing Lean source inside repository: {rel}')
    return src


def prepare(root, spec):
    if not isinstance(spec, dict) or set(spec) - {'moves', 'redirects', 'symbols', 'imports', 'file_symbols'}:
        raise ValueError('plan must contain only moves, redirects, symbols, imports, file_symbols maps')
    moves, redirects, symbols = (spec.get(k, {}) for k in ['moves', 'redirects', 'symbols'])
    if not all(isinstance(m, dict) for m in (moves, redirects, symbols)):
        raise ValueError('each plan field must be an object')
    if set(moves) & set(redirects): raise ValueError('a module cannot be moved and redirected')
    modules = {**moves, **redirects}
    if set(modules) & set(modules.values()): raise ValueError('chained/cyclic module mappings are unsupported')
    if len(set(moves.values())) != len(moves): raise ValueError('move destinations must be distinct')
    tracked = set(subprocess.check_output(['git', 'ls-files', '-z'], cwd=root).decode().split('\0'))
    for old, new in modules.items():
        src, dst = module_path(root, old), module_path(root, new)
        if not src.is_file() or str(src.relative_to(root)) not in tracked:
            raise ValueError(f'source must exist and be tracked: {old}')
        if old in moves and dst.exists(): raise ValueError(f'destination exists: {new}')
        if old in redirects and subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', str(src.relative_to(root))], cwd=root).returncode:
            raise ValueError(f'cannot remove a module with uncommitted edits: {old}')
        if old in redirects and not dst.is_file() and new not in moves.values():
            raise ValueError(f'canonical target does not exist: {new}')
    for old, new in symbols.items():
        if not isinstance(old, str) or not isinstance(new, str) or not NAME.fullmatch(old) or not NAME.fullmatch(new):
            raise ValueError('symbols must map Lean names to Lean names')
    removed = {module_path(root, n) for n in redirects}
    moved = {module_path(root, a):module_path(root, b) for a,b in moves.items()}
    file_symbols = spec.get('file_symbols', {})
    if not isinstance(file_symbols, dict): raise ValueError('file_symbols must be an object')
    for rel, mapping in file_symbols.items():
        src = source_path(root, rel)
        if src in removed:
            raise ValueError(f'file_symbols key must name a remaining Lean source: {rel}')
        if not isinstance(mapping, dict): raise ValueError('file_symbols values must be name maps')
        for old, new in mapping.items():
            if not isinstance(old, str) or not isinstance(new, str) or not NAME.fullmatch(old) or not NAME.fullmatch(new):
                raise ValueError('file_symbols must map Lean names to Lean names')
    paths = (subprocess.check_output(['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z', '--', '*.lean'], cwd=root).decode().split('\0')
             if modules or symbols else list(file_symbols))
    updates = {}
    for rel in sorted(set(paths) - {''}):
        src = root / rel
        if src in removed or not src.is_file(): continue
        source = src.read_text(); result = rewrite(source, modules, symbols | file_symbols.get(rel, {}))
        if result != source or src in moved: updates[moved.get(src, src)] = result
    import_edits = spec.get('imports', {})
    if not isinstance(import_edits, dict): raise ValueError('imports must be an object')
    for rel, rule in import_edits.items():
        src = source_path(root, rel)
        if src in removed:
            raise ValueError(f'import file must exist and remain in the tree: {rel}')
        if not isinstance(rule, dict) or set(rule) - {'add', 'remove'}:
            raise ValueError('import edits contain only add and remove arrays')
        additions, removals = rule.get('add', []), rule.get('remove', [])
        if not isinstance(additions, list) or not isinstance(removals, list):
            raise ValueError('add and remove must be arrays of project module names')
        for mod in additions + removals: module_path(root, mod)
        additions = [modules.get(mod, mod) for mod in additions]
        removals = {modules.get(mod, mod) for mod in removals}
        if set(additions) & removals: raise ValueError('cannot add and remove the same import')
        for mod in additions:
            if not module_path(root, mod).is_file() and mod not in moves.values():
                raise ValueError(f'added import does not exist: {mod}')
        dst = moved.get(src, src)
        source = updates.get(dst, rewrite(src.read_text(), modules, symbols | file_symbols.get(rel, {})))
        kept, present = [], set()
        for line, masked in zip(source.splitlines(keepends=True), code_mask(source).splitlines(keepends=True)):
            imported = IMPORT.match(masked)
            if imported:
                if imported[2] in removals: continue
                present.add(imported[2])
            kept.append(line)
        kept_mask = code_mask(''.join(kept)).splitlines(keepends=True)
        module_index = next((i + 1 for i, line in enumerate(kept_mask) if line.strip() == 'module'), 0)
        import_prefix = 'public import ' if module_index else 'import '
        insert = ''.join(import_prefix + mod + '\n' for mod in dict.fromkeys(additions) if mod not in present)
        if insert:
            # Keep the module command first, inserting new public imports beside
            # the existing imports. Existing proof/doc blocks are never moved.
            index = module_index
            if index:
                if not kept[index - 1].endswith('\n'): kept[index - 1] += '\n'
                insert = '\n' + insert
            kept.insert(index, insert)
        result = ''.join(kept)
        if result != src.read_text() or dst != src: updates[dst] = result
    return moves, redirects, updates


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('plan', type=Path)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        spec = json.loads(args.plan.read_text())
        moves, redirects, updates = prepare(root, spec)
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        parser.error(str(exc))
    report = {'moves':moves, 'redirects':redirects, 'file_symbol_edits':sorted(spec.get('file_symbols', {})),
              'updated_files':[str(p.relative_to(root)) for p in sorted(updates)], 'applied':args.apply}
    print(json.dumps(report, ensure_ascii=False, indent=2))
    if not args.apply: return
    # All semantic/file validations above happen before the first mutation.
    # git mv/rm stage only the explicit module moves/deletions; edits remain
    # unstaged for the caller's path-scoped review and commit.
    for old, new in moves.items():
        src, dst = module_path(root, old), module_path(root, new)
        dst.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['git','mv','--',str(src.relative_to(root)),str(dst.relative_to(root))],cwd=root,check=True)
    for old in redirects:
        subprocess.run(['git','rm','--',str(module_path(root,old).relative_to(root))],cwd=root,check=True)
    for path, source in updates.items(): path.write_text(source)


if __name__ == '__main__': main()
