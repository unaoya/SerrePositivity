"""層検査の構文・循環・例外・段階強制・ratchet の回帰試験。"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import layer_check as lc

HERE = Path(__file__).resolve().parent
CONFIG = json.loads((HERE / 'layers.json').read_text())
CORE = lc.IC + '.Core.Test'
F1 = lc.IC + '.F1.Test'
DG = 'SerrePositivity.DifferentialGraded.Test'


class LayerTests(unittest.TestCase):
    def test_foundation_negative_rank_and_prefix_scope(self):
        lc.validate_config(CONFIG)
        foundation = next(x for x in CONFIG['layers'] if x['name'] == 'Foundation')
        self.assertEqual(foundation['rank'], -1)
        self.assertTrue(all(x['rank'] > -1 for x in CONFIG['layers'] if x['name'] != 'Foundation'))
        self.assertEqual(len(foundation['prefixes']), 23)
        self.assertNotIn('Foundation', CONFIG['core'])
        for prefix in foundation['prefixes']:
            self.assertEqual(lc.classify(prefix, CONFIG), 'Foundation')
            self.assertEqual(lc.classify(prefix + '.Child', CONFIG), 'Foundation')
        for module in ['CategoryTheory.MonoidalUnitHom', 'CategoryTheory.SimplexChainVertices',
                       'CategoryTheory.Groupoid.Other', 'CategoryTheory.LiftingProperties.Other',
                       'CategoryTheory.MorphismProperty.Other', 'CategoryTheory.Abelian.Basic',
                       'GroupTheory.ConjugateSum']:
            self.assertIsNone(lc.classify('SerrePositivity.' + module, CONFIG))

    def test_foundation_restricted_imports(self):
        source = 'SerrePositivity.CategoryTheory.Monoidal.Test'
        for target in ['Mathlib.CategoryTheory.Category.Basic',
                       'SerrePositivity.CategoryTheory.FiniteBijectionSum',
                       'SerrePositivity.GroupTheory.Coxeter.TypeA']:
            self.assertEqual(lc.direct_reasons(source, target, CONFIG), [])
        for target in ['MathlibExtra.Basic', 'Lean', 'SerrePositivity.HomotopicalAlgebra.Test',
                       'SerrePositivity.EInfinity.Test', 'SerrePositivity.KST.Test',
                       'SerrePositivity.CategoryTheory.Abelian.Test']:
            self.assertIn('restricted-layer-import', lc.direct_reasons(source, target, CONFIG))

    def test_foundation_to_core_violates_and_ratchets(self):
        source = 'SerrePositivity.CategoryTheory.Monoidal.Test'
        reasons = lc.direct_reasons(source, CORE, CONFIG)
        self.assertEqual(set(reasons), {'upward-layer-import', 'restricted-layer-import'})
        before = lc.analyze({source: set(), CORE: set()}, set(), CONFIG)
        after = lc.analyze({source: {CORE}, CORE: set()}, set(), CONFIG)
        self.assertEqual(after['direct_by_pair']['Foundation -> Core'], 1)
        self.assertTrue(any(x['metric'] == 'report_direct/Foundation -> Core'
                            for x in lc.ratchet_increases(after, before)))

    def test_every_core_layer_can_import_foundation(self):
        target = 'SerrePositivity.GroupTheory.Coxeter.TypeA'
        for layer in CONFIG['layers']:
            if layer['name'] not in CONFIG['core']:
                continue
            source = layer['prefixes'][0] + '.Test'
            with self.subTest(layer=layer['name']):
                self.assertEqual(lc.direct_reasons(source, target, CONFIG), [])
                self.assertEqual(lc.analyze({source: {target}, target: set()}, set(), CONFIG)
                                 ['direct_violations'], [])

    def test_lean_comments_strings_and_multiline_imports(self):
        source = '''module
/- import Bad.One /- nested -/ import Bad.Two -/
public import
  SerrePositivity.InfinityCategories.Core.Test
import Mathlib.Data.Nat.Basic Mathlib.Data.Bool.Basic -- import Bad.Three
def text := "import Bad.Four /- ModelCategory -/"
def quote : Char := '"'
'''
        self.assertEqual(lc.imports(source), {CORE, 'Mathlib.Data.Nat.Basic', 'Mathlib.Data.Bool.Basic'})
        self.assertNotIn('ModelCategory', lc.code_only(source))

    def test_cyclic_closure_and_shared_dependencies(self):
        nodes, _, masks = lc.closure_masks({'A': {'B', 'D'}, 'B': {'C'}, 'C': {'B', 'D'}, 'D': set()})
        self.assertEqual(set(lc.selected_names(masks['A'], nodes)), {'A', 'B', 'C', 'D'})
        self.assertEqual(set(lc.selected_names(masks['B'], nodes)), {'B', 'C', 'D'})

    def test_staged_rules_and_indirect_dependency(self):
        graph = {CORE: {'Mathlib.Data.Nat.Basic'}, F1: {CORE, 'SerrePositivity.Other'},
                 'SerrePositivity.Other': {DG}, DG: set()}
        r = lc.analyze(graph, set(), CONFIG)
        self.assertEqual(r['tiers']['W1']['forbidden_modules'], [DG])
        self.assertEqual(r['tiers']['W1']['by_module'][F1], 1)
        self.assertEqual(r['tiers']['W1']['entry_edges'], [])
        graph[CORE] = {lc.IC + '.Kan.Test'}
        r = lc.analyze(graph, set(), CONFIG)
        self.assertEqual(r['tiers']['W1']['direct_violation_count'], 0)
        self.assertEqual(r['tiers']['W2b']['direct_by_pair']['Core -> Kan'], 1)
        self.assertEqual(lc.direct_reasons(CORE, lc.IC + '.Core.Other', CONFIG), [])

    def test_model_and_pointed_prefix_exceptions(self):
        model = 'SerrePositivity.HomotopicalAlgebra.Simplicial.Test'
        self.assertFalse(lc.forbidden(model, 'W1', CONFIG, {model}))
        self.assertTrue(lc.forbidden(model, 'W2a', CONFIG, {model}))
        self.assertFalse(lc.forbidden('SerrePositivity.Spectra.Pointed', 'W2a', CONFIG, set()))
        self.assertFalse(lc.forbidden('SerrePositivity.Spectra.Pointed.Child', 'W2a', CONFIG, set()))
        self.assertTrue(lc.forbidden(lc.IC+'.ModelBridge.Test', 'W2a', CONFIG, set()))

    def test_prefix_boundaries_and_longest_layer(self):
        self.assertFalse(lc.under(lc.IC + '.F1B.Test', lc.IC + '.F1'))
        self.assertEqual(lc.classify(lc.IC + '.F1B.Test', CONFIG), 'F1B')
        self.assertFalse(lc.under(lc.IC + '.StablePresentable.Test', lc.IC + '.Stable'))
        self.assertEqual(lc.classify(lc.IC + '.StablePresentable.Test', CONFIG), 'StablePresentable')
        self.assertFalse(lc.forbidden('SerrePositivity.Spectra.Pointed.Basic', 'W2a', CONFIG, set()))
        self.assertTrue(lc.forbidden('SerrePositivity.Spectra.PointedOther.Basic', 'W2a', CONFIG, set()))
        config = copy.deepcopy(CONFIG)
        config['layers'].append({'name': 'Nested', 'rank': 11, 'prefixes': [lc.IC + '.F1.Special']})
        self.assertEqual(lc.classify(lc.IC + '.F1.Special.Test', config), 'Nested')

    def test_expiring_edge_exception(self):
        config = copy.deepcopy(CONFIG)
        config['exceptions'] = [{'from': F1, 'to': DG, 'reason': 'test only', 'expires': 'W1'}]
        r = lc.analyze({F1: {DG}, DG: set()}, set(), config)
        self.assertEqual(r['tiers']['W1']['violation_count'], 0)
        self.assertEqual(r['tiers']['W2a']['forbidden_module_count'], 1)

    def test_ratchet_same_and_added_edge(self):
        graph = {F1: {CORE}, CORE: set(), DG: set()}
        before = lc.analyze(graph, set(), CONFIG)
        self.assertEqual(lc.ratchet_increases(before, before), [])
        graph[F1].add(DG)
        after = lc.analyze(graph, set(), CONFIG)
        increases = lc.ratchet_increases(after, before)
        self.assertTrue(any(x['metric'] == 'closure_unique/W1' for x in increases))

    def test_cli_ratchet_same_zero_increase_nonzero(self):
        evidence = HERE.parents[1] / '.lake/verify'
        evidence.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='layer-fixture-', dir=evidence) as directory:
            root = Path(directory)
            def put(name, text):
                file = root.joinpath(*name.split('.')).with_suffix('.lean')
                file.parent.mkdir(parents=True, exist_ok=True); file.write_text(text)
            put(F1, 'import ' + CORE + '\n')
            put(CORE, '-- ModelCategory inside a comment\n')
            put(DG, '')
            baseline = root / 'before.json'
            def run(*mode):
                return subprocess.run([sys.executable, str(HERE/'layer_check.py'), '--root', str(root), *mode],
                                      capture_output=True, text=True)
            report = run('--report', '--output', str(baseline))
            self.assertEqual(report.returncode, 0, report.stderr)
            same = run('--ratchet', str(baseline))
            self.assertEqual(same.returncode, 0, same.stderr)
            put(F1, 'import ' + CORE + '\npublic import\n ' + DG + '\n')
            increased = run('--ratchet', str(baseline))
            self.assertEqual(increased.returncode, 1, increased.stderr)
            self.assertIn('INCREASE', increased.stdout)
            enforced = run('--enforce', 'W1')
            self.assertEqual(enforced.returncode, 1, enforced.stderr)
            print('fixture CLI: report=0, same ratchet=0, increased ratchet=1, enforce W1=1')


if __name__ == '__main__':
    unittest.main(verbosity=2)
