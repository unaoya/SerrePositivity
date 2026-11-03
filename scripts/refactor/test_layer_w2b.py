"""W2b's approved boundary keeps inherited paths diagnostic, not invisible."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import layer_check as lc

CONFIG = json.loads(Path(__file__).with_name('layers.json').read_text())
HL = lc.IC + '.HomotopyLimits.Bridge'
A = lc.IC + '.F1.A'
B = lc.IC + '.F1.B'
CORE = lc.IC + '.Core.Test'
KST = 'SerrePositivity.KST.Dependency'


def policy(report):
    return {'config_sha256': report['config_sha256'],
            'direct_edges': [{'from': e['from'], 'to': e['to']}
                             for e in report['direct_violations']],
            'aggregate_limits': {t: {k: report['tiers'][t][k] for k in
                ('forbidden_module_count', 'affected_core_module_count')}
                for t in ('W1', 'W2a')}}


class W2bTests(unittest.TestCase):
    def setUp(self):
        self.graph = {A: {HL}, B: set(), HL: {KST}, KST: set()}
        self.before = lc.analyze(self.graph, set(), CONFIG)
        self.baseline = policy(self.before)

    def check_graph(self, graph):
        return lc.enforce_w2b(lc.analyze(graph, set(), CONFIG), self.baseline, CONFIG)

    def test_inherited_root_metric_is_diagnostic(self):
        graph = {**self.graph, A: set(), B: {HL}}
        current = lc.analyze(graph, set(), CONFIG)
        self.assertTrue(lc.ratchet_increases(current, self.before))
        self.assertEqual(lc.enforce_w2b(current, self.baseline, CONFIG)['status'], 'PASS')

    def test_core_order_violation_fails(self):
        result = self.check_graph({**self.graph, CORE: {A}})
        self.assertEqual(result['status'], 'FAIL')
        self.assertEqual(len(result['core_order_violations']), 1)

    def test_new_forbidden_edge_fails_even_if_total_is_unchanged(self):
        result = self.check_graph({**self.graph, HL: set(), A: {KST}})
        self.assertEqual(result['status'], 'FAIL')
        self.assertEqual([(e['from'], e['to']) for e in result['new_direct_edges']], [(A, KST)])

    def test_affected_core_increase_fails(self):
        result = self.check_graph({**self.graph, B: {HL}})
        self.assertEqual(result['status'], 'FAIL')
        self.assertTrue(any(x['metric'] == 'affected_core_module_count'
                            for x in result['aggregate_increases']))

    def test_unique_forbidden_increase_fails(self):
        other = 'SerrePositivity.KST.Other'
        result = self.check_graph({**self.graph, KST: {other}, other: set()})
        self.assertEqual(result['status'], 'FAIL')
        self.assertTrue(any(x['metric'] == 'forbidden_module_count'
                            for x in result['aggregate_increases']))

    def test_cli_uses_explicit_contract(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph = {**self.graph, A: set(), B: {HL}}
            for name, deps in graph.items():
                path = root / (name.replace('.', '/') + '.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(''.join('import ' + d + '\n' for d in deps))
            baseline = root / 'baseline.json'
            baseline.write_text(json.dumps(self.baseline))
            result = subprocess.run([sys.executable, str(Path(lc.__file__)),
                '--root', str(root), '--enforce', 'W2b', '--w2b-baseline', str(baseline)],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            saved = json.loads((root / '.lake/verify/layers.json').read_text())
            self.assertEqual(saved['w2b_enforcement']['status'], 'PASS')


if __name__ == '__main__':
    unittest.main()
