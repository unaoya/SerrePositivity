#!/usr/bin/env python3
"""Typecheck one draft in an isolated library, inside a caller-held build slot.

--setup is the JSON emitted by `lake --no-build setup-file <library source>`.
Original draft dependencies are explicit; failed/stale dependencies are rejected.
No build lock is acquired here. Use the normal with_build_lock.sh wrapper.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import subprocess
import sys
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--state', type=Path, required=True)
    parser.add_argument('--setup', type=Path, required=True)
    parser.add_argument('draft', help='Relative path without .lean, e.g. Sheaves/SheafCondition')
    parser.add_argument('dependencies', nargs='*')
    args = parser.parse_args()
    root, state = args.root.resolve(), args.state.resolve()
    drafts = root / 'formalization-plans/bhatt-scholze/drafts'
    virtual = state / 'validation'

    def relative(name):
        p = Path(name)
        if p.is_absolute() or '..' in p.parts or p.suffix:
            raise ValueError('Expected a relative draft path without an extension: ' + name)
        return p

    def receipt_path(name):
        relative(name)
        return state / ('validate-' + name.replace('/', '-') + '.json')

    def artifact(name):
        return virtual / 'Bulk5InfDraft' / relative(name).with_suffix('.olean')

    checked = set()

    def verify(name):
        if name in checked:
            return
        checked.add(name)
        r = json.loads(receipt_path(name).read_text())
        if (r['status'] != 'PASS' or not artifact(name).exists()
                or sha(drafts / relative(name).with_suffix('.lean')) != r['source_sha256']):
            raise ValueError('Stale or failed dependency: ' + name)
        if r.get('olean_sha256') and sha(artifact(name)) != r['olean_sha256']:
            raise ValueError('Changed dependency artifact: ' + name)
        for signature in r.get('dependency_signatures', []):
            dep = signature['draft']
            if (sha(drafts / relative(dep).with_suffix('.lean')) != signature['source_sha256']
                    or sha(artifact(dep)) != signature['olean_sha256']):
                raise ValueError('Dependency changed since parent was checked: ' + name + ' -> ' + dep)
        for dep in r['extra_public_imports']:
            verify(dep)

    for dep in args.dependencies:
        verify(dep)
    signatures = [{'draft': d, 'source_sha256': sha(drafts / relative(d).with_suffix('.lean')),
                   'olean_sha256': sha(artifact(d))} for d in args.dependencies]
    source = drafts / relative(args.draft).with_suffix('.lean')
    original = source.read_bytes()
    original_hash = hashlib.sha256(original).hexdigest()
    staged = original.decode()
    imports = ''.join('public import Bulk5InfDraft.' + d.replace('/', '.') + '\n'
                      for d in args.dependencies)
    if imports:
        if len(re.findall(r'^module$', staged, flags=re.MULTILINE)) != 1:
            raise ValueError('Expected one module header: ' + args.draft)
        staged = re.sub(r'^module$', lambda _: 'module\n' + imports.rstrip('\n'), staged, count=1, flags=re.MULTILINE)
    target = virtual / 'Bulk5InfDraft' / relative(args.draft).with_suffix('.lean')
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(staged)
    baseline = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=root,
                                       text=True).strip()
    options = json.loads(args.setup.read_text())['options']
    flags = ['-D' + k + '=' + ('true' if v is True else 'false' if v is False else str(v))
             for k, v in options.items()]
    command = ['lake', 'env', 'env', 'LEAN_PATH=' + str(virtual) + ':' + baseline,
               'lean', *flags, '--root=' + str(virtual), '-o', str(artifact(args.draft)), str(target)]
    log = state / ('validate-' + args.draft.replace('/', '-') + '.log')
    started = time.monotonic()
    with log.open('w') as stream:
        run = subprocess.run(command, cwd=root, stdout=stream, stderr=subprocess.STDOUT)
    dependencies_unchanged = all(
        sha(drafts / relative(d['draft']).with_suffix('.lean')) == d['source_sha256']
        and sha(artifact(d['draft'])) == d['olean_sha256'] for d in signatures)
    unchanged = sha(source) == original_hash and dependencies_unchanged
    code = run.returncode if unchanged else 76
    result = dict(draft=str(source.relative_to(root)), source_sha256=original_hash,
                  staged_source_sha256=sha(target), source_unchanged_during_check=unchanged,
                  dependencies_unchanged_during_check=dependencies_unchanged,
                  dependency_signatures=signatures, extra_public_imports=args.dependencies,
                  options=options, command=command, lean_exit_code=run.returncode,
                  exit_code=code, seconds=time.monotonic() - started,
                  status='STALE' if not unchanged else 'PASS' if code == 0 else 'FAIL',
                  olean=str(artifact(args.draft)) if code == 0 else None,
                  olean_sha256=sha(artifact(args.draft)) if code == 0 else None)
    receipt_path(args.draft).write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(result, ensure_ascii=False), flush=True)
    return code


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, FileNotFoundError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(66)
