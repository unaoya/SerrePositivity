#!/usr/bin/env python3
"""空の snapshot の比較、および実 Lean の空選択・証明依存を検査する。"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import unittest
from compare_snapshots import compare

EMPTY = {'schema_version': 1, 'count': 0, 'declarations': []}
ROW = {'name': 'A.x', 'parent': 'A.x', 'kind': 'def', 'type': ['sort', 0],
       'body': ['lit', 1], 'axioms': [], 'attributes': {}}
ONE = {'schema_version': 1, 'count': 1, 'declarations': [ROW]}

class EmptyComparison(unittest.TestCase):
    def test_both_empty(self):
        self.assertEqual(compare(EMPTY, EMPTY), {'status': 'PASS', 'before_count': 0,
            'after_count': 0, 'parent_count': 0, 'changes': [], 'transient': {'before': [], 'after': []}})

    def test_removed(self):
        result = compare(ONE, EMPTY)
        self.assertEqual(result['status'], 'FAIL')
        self.assertEqual(result['changes'], [{'name': 'A.x', 'change': 'removed'}])

    def test_added(self):
        result = compare(EMPTY, ONE)
        self.assertEqual(result['status'], 'FAIL')
        self.assertEqual(result['changes'], [{'name': 'A.x', 'change': 'added'}])


def integration():
    root = Path(__file__).resolve().parents[2]
    out = root / '.lake/verify/ifw0-3-roof/empty-tests'
    out.mkdir(parents=True, exist_ok=True)
    module = 'SerrePositivity.IFW03EmptySnapshotTest'
    path = root / (module.replace('.', '/') + '.lean')
    if path.exists(): raise RuntimeError('fixture already exists')
    commands = []
    def run(label, args, expected=0):
        with (out / (label + '.log')).open('w') as log:
            proc = subprocess.run(args, cwd=root, stdout=log, stderr=subprocess.STDOUT)
        commands.append({'label': label, 'command': args, 'exit_code': proc.returncode,
                         'expected': expected})
        (out/'commands.json').write_text(json.dumps(commands, indent=2)+'\n')
        if proc.returncode != expected: raise RuntimeError(f'{label}: exit {proc.returncode}')
    def snapshot(label):
        run(label+'-build', ['lake','build',module])
        run(label, ['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean',
                    '--modules',module,'--output',str(out/(label+'.json'))])
        return json.loads((out/(label+'.json')).read_text())
    try:
        path.write_text('import Lean\n')
        empty = snapshot('empty')
        assert empty['count'] == 0 and empty['declarations'] == []
        path.write_text('import Lean\nnamespace IFW03Snapshot\ntheorem proof : True := True.intro\nend IFW03Snapshot\n')
        one = snapshot('one')
        assert one['count'] == 1
        row = one['declarations'][0]
        assert 'True.intro' in row['used_constants']
        assert row['uses_modules'] and row['uses_modules'] == row['used_modules']
        for label, before, after, expected, change in [
            ('same-empty', 'empty', 'empty', 0, None),
            ('added', 'empty', 'one', 1, 'added'),
            ('removed', 'one', 'empty', 1, 'removed')]:
            run(label, [sys.executable, 'scripts/refactor/compare_snapshots.py',
                str(out/(before+'.json')), str(out/(after+'.json')),
                '--output', str(out/(label+'.json'))], expected)
            result = json.loads((out/(label+'.json')).read_text())
            assert result['changes'] == ([] if change is None else
                [{'name': 'IFW03Snapshot.proof', 'module': module, 'change': change}])
        (out/'status.txt').write_text('PASS\n')
        print('PASS: empty Lean module, proof dependencies, empty/added/removed CLI comparisons')
    finally:
        path.unlink(missing_ok=True)
        for base in ['.lake/build/lib/lean', '.lake/build/ir']:
            stem = root/base/module.replace('.', '/')
            for artifact in stem.parent.glob(stem.name+'.*'):
                if artifact.is_file(): artifact.unlink()

if __name__ == '__main__':
    if '--integration' in sys.argv: integration()
    else: unittest.main()
