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
