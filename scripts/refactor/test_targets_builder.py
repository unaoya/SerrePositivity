#!/usr/bin/env python3
"""閉包に合わない候補を JSON に含めないことを小さいグラフで検査する。"""
import json
from pathlib import Path
import unittest
import targets_builder as tb

C=json.loads(Path(__file__).with_name('layers.json').read_text())
I=tb.IC

def p(dest): return dict(dest=dest)

class ClosureTests(unittest.TestCase):
    def test_same_layer_dependency(self):
        g={'SerrePositivity.X.A':{I+'.Core.B'}, I+'.Core.B':{'Mathlib.X'}}
        ok,e=tb.closed_moves(g,{'SerrePositivity.X.A':p(I+'.Core.A')},C)
        self.assertEqual(ok,{'SerrePositivity.X.A'})
        self.assertEqual(e['SerrePositivity.X.A']['closure_count'],2)
    def test_transitive_upward(self):
        g={'SerrePositivity.X.A':{I+'.Core.B'},I+'.Core.B':{I+'.F1.C'}}
        ok,e=tb.closed_moves(g,{'SerrePositivity.X.A':p(I+'.Core.A')},C)
        self.assertFalse(ok)
        self.assertEqual(e['SerrePositivity.X.A']['witness'],['SerrePositivity.X.A',I+'.Core.B',I+'.F1.C'])
    def test_simultaneous_moves(self):
        g={'SerrePositivity.X.A':{'SerrePositivity.X.B'},'SerrePositivity.X.B':{'Mathlib.X'}}
        ps={n:p(I+'.Core.'+n.rsplit('.',1)[1]) for n in g}
        self.assertEqual(tb.closed_moves(g,ps,C)[0],set(g))
    def test_failed_dependency_propagates(self):
        g={'SerrePositivity.X.A':{'SerrePositivity.X.B'},'SerrePositivity.X.B':{I+'.F2.C'}}
        ps={n:p(I+'.Core.'+n.rsplit('.',1)[1]) for n in g}
        self.assertFalse(tb.closed_moves(g,ps,C)[0])
    def test_collision_propagates(self):
        g={'SerrePositivity.X.A':{'SerrePositivity.X.B'},'SerrePositivity.X.B':set()}
        ps={n:p(I+'.Core.'+n.rsplit('.',1)[1]) for n in g}
        self.assertFalse(tb.closed_moves(g,ps,C,{'SerrePositivity.X.B'})[0])
    def test_unknown_repository_not_implicitly_allowed(self):
        self.assertTrue(tb.disallowed(I+'.F1.A','SerrePositivity.KST.X',C))
    def test_w1_forbidden(self):
        self.assertTrue(tb.disallowed(I+'.Stable.A',I+'.Derived.B',C))
    def test_simplicial_cannot_import_core(self):
        self.assertTrue(tb.disallowed(I+'.Simplicial.A',I+'.Core.B',C))
    def test_equal_rank_and_prefix_boundary(self):
        self.assertFalse(tb.disallowed(I+'.F1.A',I+'.F1B.B',C))
        self.assertTrue(tb.disallowed(I+'.Stable.A',I+'.StablePresentable.B',C))
    def test_renames_consumers(self):
        self.assertEqual(tb.renamed_graph({'A':{'B'},'B':set()},{'B':'C'}),{'A':{'C'},'C':set()})

class SimulationTests(unittest.TestCase):
    def test_remove_edge_and_input_unchanged(self):
        g={'A':{'B'},'B':set()}
        self.assertEqual(tb.edit_edges(g,[{'from':'A','to':'B'}]),{'A':set(),'B':set()})
        self.assertEqual(g['A'],{'B'})
    def test_remove_after_rename(self):
        self.assertEqual(tb.edit_edges({'A':{'C'},'C':set()},[{'from':'A','to':'B'}],renames={'B':'C'})['A'],set())
    def test_bad_removed_edge(self):
        with self.assertRaisesRegex(ValueError,'does not exist'):tb.edit_edges({'A':set()},[{'from':'A','to':'B'}])
    def test_duplicate_removed_edge(self):
        with self.assertRaisesRegex(ValueError,'duplicate'):tb.edit_edges({'A':{'B'}},[{'from':'A','to':'B'}]*2)
    def test_add_edge_and_reject_typo(self):
        self.assertEqual(tb.edit_edges({'A':set(),'SerrePositivity.B':set()},additions=[{'from':'A','to':'SerrePositivity.B'}])['A'],{'SerrePositivity.B'})
        with self.assertRaisesRegex(ValueError,'target'):tb.edit_edges({'A':set()},additions=[{'from':'A','to':'SerrePositivity.Missing'}])
    def test_transitive_users_exclude_self(self):
        self.assertEqual(tb.transitive_users({'A':{'B'},'B':{'C'},'C':set()},'C'),['A','B'])
    def test_pull_down_60_limit(self):
        g={I+'.F2.A':{I+'.F2.X'+str(i) for i in range(60)}}
        g.update({n:set() for n in g[I+'.F2.A']})
        r=tb.pull_down(g,I+'.F2.A',I+'.F1.A',C,set())
        self.assertEqual(r['count'],61);self.assertFalse(r['within_limit'])
    def test_pull_down_rejects_model_even_below_limit(self):
        model='SerrePositivity.HomotopicalAlgebra.Custom'
        r=tb.pull_down({I+'.F2.A':{model}},I+'.F2.A',I+'.F1.A',C,{model})
        self.assertEqual(r['polluted'],[model]);self.assertTrue(r['within_limit'])
    def test_current_and_conditional_future_are_distinct(self):
        import argparse,contextlib,io,tempfile
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); (root/'scripts/refactor').mkdir(parents=True)
            (root/'scripts/refactor/layers.json').write_text(json.dumps(C))
            for n,src in [(I+'.Core.Root','import '+I+'.Derived.A'),(I+'.Derived.A','import SerrePositivity.DifferentialGraded.D'),('SerrePositivity.DifferentialGraded.D','def d := 1')]:
                p=root/(n.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(src+'\n')
            def entry(n,d):return dict(module=n,dest=d,action='move',moved=[],keep=[],attributes={},candidate='fixture',note='graph fixture')
            current=root/'current.json';current.write_text(json.dumps([entry(I+'.Derived.A',I+'.Core.A')]))
            future=root/'future.json';future.write_text(json.dumps([entry('SerrePositivity.DifferentialGraded.D',I+'.Core.D')]))
            args=argparse.Namespace(root=root,plans=[current],future_plans=[future],remove_edges=None,add_edges=None,snapshot=[],output_dir=root/'out')
            with contextlib.redirect_stdout(io.StringIO()):tb.simulate_plans(args)
            r=json.loads((root/'out/simulation.json').read_text())
            self.assertFalse(r['conditions']['manual']['passes'])
            self.assertTrue(r['conditions']['conditional_future']['passes'])
            self.assertEqual(r['conditions']['manual']['counts']['DifferentialGraded'],1)

class W1ConditionTests(unittest.TestCase):
    def test_no_dg_is_insufficient_if_layer_violations_increase(self):
        import layer_check as lc
        baseline=lc.analyze({I+'.Core.A':set(),I+'.F2.B':set()},set(),C)
        after=lc.analyze({I+'.Core.A':{I+'.F2.B'},I+'.F2.B':set()},set(),C)
        result=tb.w1_condition(after,baseline)
        self.assertEqual(result['counts'],{'DifferentialGraded':0,'EInfinity':0})
        self.assertFalse(result['passes']);self.assertFalse(result['direct_not_increased'])

class ManualModuleTests(unittest.TestCase):
    def test_duplicate_redirect_and_body_imports(self):
        graph={'Old':{'Dep'},'New':{'Old'},'User':{'Old'},'Dep':set()}
        result=tb.manual_modules(graph,{'redirects':{'Old':'New'},'imports':{'New':['Dep']}})
        self.assertEqual(result,{'New':{'Dep'},'User':{'New'},'Dep':set()})
        self.assertEqual(graph['New'],{'Old'})
    def test_unreplaced_stub_rejected(self):
        with self.assertRaisesRegex(ValueError,'self import'):
            tb.manual_modules({'Old':set(),'New':{'Old'}},{'redirects':{'Old':'New'}})
    def test_missing_redirect_rejected(self):
        with self.assertRaisesRegex(ValueError,'existing'):
            tb.manual_modules({'A':set()},{'redirects':{'A':'Missing'}})

class RoofTests(unittest.TestCase):
    def test_derived_only_closure_and_leaks(self):
        seeds=[I+'.Derived.'+n for n in ('SliceEvaluationPinched','RightFibrationTerminalRepresentation','RoofTargetFunctor')]
        extra=I+'.Derived.Bad';outside=I+'.Core.Outside'
        graph={seeds[0]:{extra,outside},seeds[1]:set(),seeds[2]:set(),extra:set(),outside:{I+'.Derived.Unreachable'}}
        result=tb.roof_cluster(graph,lambda m:'def x : DGCategory := y' if m==extra else '-- DG in comment\ndef x := 1')
        self.assertEqual(set(result['derived_closure']),set(seeds+[extra]))
        self.assertEqual(set(result['cluster']),set(seeds))
        self.assertEqual(result['leaks'],[{'from':seeds[0],'to':extra}])
    def test_identifier_boundaries_exclude_quasicategory_words(self):
        seeds=[I+'.Derived.'+n for n in ('SliceEvaluationPinched','RightFibrationTerminalRepresentation','RoofTargetFunctor')]
        result=tb.roof_cluster({m:set() for m in seeds},lambda m:'def pointEdge := FullSubcomplex Subcomplex Simplex Complex Module MyDGCategory')
        self.assertEqual(set(result['cluster']),set(seeds))
        self.assertEqual(result['excluded'],{})
    def test_exact_dg_markers(self):
        seeds=[I+'.Derived.'+n for n in ('SliceEvaluationPinched','RightFibrationTerminalRepresentation','RoofTargetFunctor')]
        for token in ('DGCategory','DGFunctor','dgNerve','dgClosedEdge','DG','dg','Cochain','HomologicalComplex','ChainComplex','ModuleCat','CommRing','Bimodule'):
            result=tb.roof_cluster({m:set() for m in seeds},lambda m:'def x := '+token)
            self.assertEqual(result['cluster'],[],token)

if __name__=='__main__': unittest.main()
