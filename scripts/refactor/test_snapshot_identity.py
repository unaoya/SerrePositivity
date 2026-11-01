import unittest
from snapshot_identity import combine_rows
from compare_snapshots import compare

class IdentityTest(unittest.TestCase):
    def test_environment_overrides_position_but_source_twins_survive(self):
        def row(n, m):
            return dict(name=n, module=m, kind='theorem', parent=n, type=['sort',0], body=None, axioms=[], attributes={})
        rows, skipped = combine_rows([(row('gen','X'),True),(row('gen','Y'),False),
                                      (row('t','X'),False),(row('t','Y'),False)], {'gen':'Y'})
        self.assertEqual(set(rows),{('gen','Y'),('t','X'),('t','Y')})
        self.assertEqual(skipped,{('gen','Y')})
        before=dict(schema_version=1,declarations=[rows['t','X'],rows['t','Y']])
        after=dict(schema_version=1,declarations=[row('t','Z'),row('t','Y')])
        self.assertEqual(compare(before,after,module_map={'modules':{'X':'Z'}})['before_count'],2)
        self.assertEqual(compare(before,after,module_map={'modules':{'X':'Z'}})['status'],'PASS')
        after['declarations'][1]['axioms']=['sorryAx']
        self.assertEqual(compare(before,after,module_map={'modules':{'X':'Z'}})['changes'][0]['module'],'Y')

    def test_private_collision_guard(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from snapshot_identity import private_collisions
        with TemporaryDirectory() as tmp:
            for mod in ('X','Y'):
                (Path(tmp)/(mod+'.lean')).write_text('private def proof_12 := 1\n')
            names = ('N.match_1.eq_2', 'N.proof_12', 'N.helper')
            candidates = {n:[dict(raw=f'_private.{m}.0.{n}',module=m) for m in ('X','Y')] for n in names}
            groups = private_collisions(candidates,tmp)
            self.assertEqual({n for n,g in groups.items() if g['generated']},{names[0]})
            rows, skipped = combine_rows([(dict(name=n,module=m),True) for m in ('X','Y') for n in names],{},groups)
            self.assertEqual(len(rows),6)
            self.assertEqual(skipped,{(names[0],'X'),(names[0],'Y')})
            self.assertEqual(groups[names[0]]['aliases'],candidates[names[0]])

    def test_embedded_generated_module_names_preserve_hash_checks(self):
        from copy import deepcopy
        from compare_snapshots import normalize_generated_name
        old, new = 'Pkg.Old.Mod', 'Pkg.New.Mod'
        names = ['N._aux_Pkg_Old_Mod___macroRules__private_Pkg_Old_Mod_0_N_termP_1',
                 'N._aux_Pkg_Old_Mod___unexpand_N_f_1']
        for name in names:
            self.assertEqual(normalize_generated_name(name, {old: new}),
                             name.replace('Pkg_Old_Mod', 'Pkg_New_Mod'))
        def row(name, mod):
            return dict(name=name, module=mod, parent=name, kind='def',
                        type_hash='type', body_hash='body', axioms=[], attributes={})
        before = dict(schema_version=2, name_map={}, hash_algorithm='test',
                      transient_rows=[], declarations=[row(n, old) for n in names])
        after = deepcopy(before)
        after['declarations'] = [row(n.replace('Pkg_Old_Mod', 'Pkg_New_Mod'), new) for n in names]
        # A per-declaration destination also covers a split rather than a move.
        module_map = {'declarations': {old: {n: new for n in names}}}
        self.assertEqual(compare(before, after, module_map=module_map)['status'], 'PASS')
        after['declarations'][0]['body_hash'] = 'changed'
        self.assertEqual(compare(before, after, module_map=module_map)['changes'], [])
        self.assertEqual(len(compare(before, after, module_map=module_map)['transient']['before']), 2)
        for name in ['N.Pkg_Old_Mod', 'N._aux_Pkg_Old_ModExtra___unexpand_N_f_1',
                     'N._aux_Pkg_Old_Mod___authored']:
            self.assertEqual(normalize_generated_name(name, {old: new}), name)

    def test_notation_auxiliary_guard_and_authored_names(self):
        from snapshot_identity import notation_auxiliary
        name = 'N._aux_Pkg_Mod___macroRules__private_Pkg_Mod_0_N_termP_1'
        self.assertTrue(notation_auxiliary(name, 'Pkg.Mod'))
        self.assertTrue(notation_auxiliary('N._aux_Pkg_Mod___unexpand_N_f_1', 'Pkg.Mod'))
        self.assertFalse(notation_auxiliary(name, 'Pkg.ModExtra'))
        self.assertFalse(notation_auxiliary(name, 'Pkg.Mod', {name}))
        self.assertFalse(notation_auxiliary('N._aux_Pkg_Mod___authored', 'Pkg.Mod'))
        row = dict(name='N.math', module='Pkg.Mod', parent='N.math', kind='def',
                   type=['sort', 0], body=['sort', 0], axioms=[], attributes={})
        before = dict(schema_version=1, declarations=[row])
        after = dict(schema_version=1, declarations=[dict(row, body=['sort', 1])])
        self.assertEqual(compare(before, after)['changes'][0]['change'], 'body')

    def test_anonymous_instance_identity_ignores_only_numbering(self):
        from snapshot_identity import match_anonymous_instances
        before = [dict(name='N.instI_2', module='M', type_pp='I X', anonymous_instance=True)]
        after = [dict(before[0], name='N.instI_5')]
        self.assertEqual(match_anonymous_instances(before, after)[0]['after'], 'N.instI_5')
        for changed in [dict(after[0], module='Other'), dict(after[0], type_pp='I Y'),
                        dict(after[0], anonymous_instance=False)]:
            with self.assertRaises(ValueError):
                match_anonymous_instances(before, [changed])
        with self.assertRaises(ValueError):
            match_anonymous_instances(before, after + after)
