#!/usr/bin/env python3
"""保存検査の実 Lean 試験。専用 worktree の一時モジュールを必ず片付ける。"""
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / '.lake/verify/ifw0-2-preservation'
BASE = '''import Lean
namespace IFW0Snapshot.Old
def b : Bool := false
def c (n : Nat) : Nat := n
@[simp] theorem c_eq (n : Nat) : c n = n := rfl
opaque token : Bool := false
@[reducible] def wrapped : Bool := b
instance (priority := 1200) sampleInstance : Inhabited Bool := ⟨false⟩
private def hidden : Bool := false
def publicHidden : Bool := hidden
end IFW0Snapshot.Old
'''


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    modules = ['SerrePositivity.IFW0Snapshot', 'SerrePositivity.IFW0SnapshotMoved']
    files = [ROOT / (m.replace('.', '/') + '.lean') for m in modules]
    if any(p.exists() for p in files): raise RuntimeError('fixture path already exists')
    results = []
    def run(label, argv, expected=0):
        started = time.monotonic()
        with (OUT / (label + '.log')).open('w') as log:
            rc = subprocess.call(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        row = {'label': label, 'command': argv, 'exit_code': rc, 'expected': expected,
               'seconds': round(time.monotonic()-started, 3)}
        results.append(row)
        (OUT/'commands.json').write_text(json.dumps(results, indent=2)+'\n')
        print(json.dumps(row), flush=True)
        if rc != expected: raise RuntimeError(f'{label}: unexpected exit {rc}, see {OUT/(label+".log")}')
    def snapshot(label, module):
        run(label+'-build', ['lake', 'build', module])
        run(label, ['lake', 'env', 'lean', '--run', 'scripts/refactor/decl_snapshot.lean',
                    '--modules', module, '--output', str(OUT/(label+'.json'))])
    def compare(label, other, expected, mapping=None):
        args = [sys.executable, 'scripts/refactor/compare_snapshots.py', str(OUT/'before.json'),
                str(OUT/(other+'.json')), '--output', str(OUT/(label+'.json'))]
        if mapping: args += ['--name-map', str(mapping)]
        run(label, args, expected)
        return json.loads((OUT/(label+'.json')).read_text())
    try:
        files[0].write_text(BASE)
        snapshot('before', modules[0])
        rows = {r['name']: r for r in json.loads((OUT/'before.json').read_text())['declarations']}
        assert rows['IFW0Snapshot.Old.token']['body'] is not None
        assert rows['IFW0Snapshot.Old.sampleInstance']['attributes']['instance_priority'] == 1200
        assert rows['IFW0Snapshot.Old.c_eq']['attributes']['simp'] is True
        files[0].write_text(BASE.replace('def b : Bool := false', 'def b : Bool := true'))
        snapshot('body-changed', modules[0])
        result = compare('compare-body', 'body-changed', 1)
        assert any(r['name']=='IFW0Snapshot.Old.b' and r['change']=='body' for r in result['changes'])
        files[0].write_text(BASE.replace('@[simp] theorem', 'theorem'))
        snapshot('simp-removed', modules[0])
        result = compare('compare-simp', 'simp-removed', 1)
        assert any(r['name']=='IFW0Snapshot.Old.c_eq' and r['change']=='attributes' for r in result['changes'])
        files[0].write_text(BASE)
        files[1].write_text(BASE.replace('IFW0Snapshot.Old', 'IFW0Snapshot.New'))
        snapshot('renamed', modules[1])
        mapping = OUT/'names.json'; mapping.write_text(json.dumps({'IFW0Snapshot.Old': 'IFW0Snapshot.New'})+'\n')
        result = compare('compare-renamed', 'renamed', 0, mapping)
        assert result['changes'] == []
        (OUT/'status.txt').write_text('PASS\n')
        print('PASS: body change, simp removal, namespace relocation, opaque value, instance priority', flush=True)
    finally:
        for p in files: p.unlink(missing_ok=True)
        for mod in modules:
            for base in [ROOT/'.lake/build/lib/lean', ROOT/'.lake/build/ir']:
                stem = base / mod.replace('.', '/')
                for p in stem.parent.glob(stem.name+'.*'):
                    if p.is_file(): p.unlink()


if __name__ == '__main__': main()
