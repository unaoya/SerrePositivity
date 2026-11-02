"""DG-W2 §16 regression. DG_W2_LEAN_TEST=1 enables the locked Lean check."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import unittest

import merge_modules as mm
from compare_snapshots import compare

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / '.lake/verify/merge-universe-order'


class UniverseOrderTest(unittest.TestCase):
    @unittest.skipUnless(os.environ.get('DG_W2_LEAN_TEST') == '1', 'opt-in: DG_W2_LEAN_TEST=1')
    def test_opposite_universe_orders_preserve_types(self):
        command = ['zsh', str(ROOT/'scripts/refactor/with_build_lock.sh'), '--wait', '0', '--',
                   sys.executable, '-B', str(Path(__file__).resolve()), '--worker']
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        if result.returncode == 75:
            self.skipTest('build lock busy; Lean test deferred')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


def worker():
    OUT.mkdir(parents=True, exist_ok=True)
    search = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, text=True).strip()
    env = {**os.environ, 'LEAN_PATH': str(OUT) + ':' + search}
    commands = []

    def run(label, args, cwd=OUT):
        started = time.monotonic()
        result = subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True)
        text = result.stdout + result.stderr
        (OUT/(label+'.log')).write_text(text)
        commands.append(dict(label=label, exit_code=result.returncode,
                             seconds=round(time.monotonic()-started, 3)))
        (OUT/'commands.json').write_text(json.dumps(commands, indent=2)+'\n')
        if result.returncode or re.search(r'(?m)^PANIC\b|\berror(?:\([^)]*\))?:', text):
            raise RuntimeError(label+'\n'+text)
        return text

    parts = []
    for module, order, name in [('UniverseBeforeA', 'v u', 'first'), ('UniverseBeforeB', 'u v', 'second')]:
        source = ('module\npublic import Mathlib.Data.Nat.Basic\n@[expose] public section\n'
                  'universe '+order+'\nnamespace DGUniverseOrder\n'
                  'def '+name+' (α : Type u) (β : Type v) := α × β\n'
                  'def '+name+'Id (α : Type u) (β : Type v) (x : '+name+' α β) : '+name+' α β := x\n'
                  'end DGUniverseOrder\n')
        (OUT/(module+'.lean')).write_text(source)
        parts.append(mm.parse_part(module, source))
        run(module, ['lean', '-o', module+'.olean', module+'.lean'])
    entry = dict(module='UniverseMerged', docstring='# Universe-order preservation')
    merged, _ = mm.render_group(entry, parts, {})
    assert 'universe' not in merged.split('@[expose] public section UniverseBeforeA')[0]
    for module, order in [('UniverseBeforeA', 'v u'), ('UniverseBeforeB', 'u v')]:
        assert '@[expose] public section '+module+'\nuniverse '+order+'\n' in merged
    (OUT/'UniverseMerged.lean').write_text(merged)
    run('merged', ['lean', '-o', 'UniverseMerged.olean', 'UniverseMerged.lean'])
    # A negative control models the former union-at-the-top implementation.
    bad = re.sub(r'(?m)^universe .*\n', '', merged)
    bad = bad.replace('@[expose] public section UniverseBeforeA',
                      'universe v u\n@[expose] public section UniverseBeforeA', 1)
    (OUT/'UniverseHoisted.lean').write_text(bad)
    run('hoisted', ['lean', '-o', 'UniverseHoisted.olean', 'UniverseHoisted.lean'])

    def snapshot(label, modules):
        output = OUT/(label+'.json')
        run(label, ['lean', '-M', '40000', '--run', str(ROOT/'scripts/refactor/decl_snapshot.lean'),
                    '--modules', ','.join(modules), '--output', str(output)])
        return json.loads(output.read_text())

    before = snapshot('before', ['UniverseBeforeA', 'UniverseBeforeB'])
    after = snapshot('after', ['UniverseMerged'])
    hoisted = snapshot('hoisted-snapshot', ['UniverseHoisted'])
    mapping = {'modules': {p.module: 'UniverseMerged' for p in parts}}
    result = compare(before, after, module_map=mapping)
    (OUT/'comparison.json').write_text(json.dumps(result, indent=2)+'\n')
    assert result['status'] == 'PASS', result['changes']
    old_rows = {r['name']: r for r in before['declarations']}
    new_rows = {r['name']: r for r in after['declarations']}
    for name in ['first', 'firstId', 'second', 'secondId']:
        key = 'DGUniverseOrder.'+name
        assert old_rows[key]['type_hash'] == new_rows[key]['type_hash'], key
    negative = compare(before, hoisted, module_map={'modules': {p.module: 'UniverseHoisted' for p in parts}})
    assert any(c['change'] == 'type' and c['name'] == 'DGUniverseOrder.secondId'
               for c in negative['changes']), negative
    (OUT/'negative-control.json').write_text(json.dumps(negative, indent=2)+'\n')
    # Explicitly printed universe arguments also retain their order.
    prints = {}
    for label, modules in [('before', ['UniverseBeforeA', 'UniverseBeforeB']), ('after', ['UniverseMerged'])]:
        text = 'module\n'+''.join('import all '+m+'\n' for m in modules)
        text += '#check DGUniverseOrder.firstId\n#check DGUniverseOrder.secondId\n'
        path = OUT/(label+'-check.lean'); path.write_text(text)
        prints[label] = run(label+'-check', ['lean', str(path)])
    assert prints['before'] == prints['after'], prints
    (OUT/'summary.json').write_text(json.dumps(dict(status='PASS', declarations=4,
         type_hashes_equal=True, universe_order_equal=True, hoisted_control_rejected=True), indent=2)+'\n')


if __name__ == '__main__':
    if sys.argv[1:] == ['--worker']:
        worker()
    else:
        unittest.main()
