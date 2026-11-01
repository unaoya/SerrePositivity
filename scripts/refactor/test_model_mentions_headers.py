import json,tempfile,unittest
from pathlib import Path
import layer_check as lc
from validate_targets import validate, ROOT

class HeaderMentions(unittest.TestCase):
    def test_split_header_replacement_matches_real_graph(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            module='SerrePositivity.HomotopicalAlgebra.Simplicial.Example'
            dest='SerrePositivity.InfinityCategories.Core.Split'
            core='SerrePositivity.InfinityCategories.Core.Entry'
            text='module\npublic import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant\ndef keep : Nat := 0\ndef moved : Nat := 1\n'
            def put(name,text):
                p=root/(name.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
            put(module,text);put(core,'import '+module+'\n')
            entry=dict(action='split',module=module,dest=dest,moved=['moved'],keep=['keep'],attributes={},candidate='test',note='test',
                       imports={module:['Mathlib.Data.Nat.Basic'],dest:['Mathlib.Data.Nat.Basic']})
            snap={'sources':[{'module':module,'source':text}],'declarations':[dict(name=n,module=module,used_constants=[]) for n in ['keep','moved']]}
            config=json.loads((ROOT/'scripts/refactor/layers.json').read_text())
            result,_,graph,_,mentions=validate(root,[entry],{module:snap},config,return_graph=True)
            self.assertEqual(result['before']['closure']['W2a'],1)
            self.assertEqual(result['after']['closure']['W2a'],0)
            put(module,'module\npublic import Mathlib.Data.Nat.Basic\ndef keep : Nat := 0\n')
            put(dest,'module\npublic import Mathlib.Data.Nat.Basic\ndef moved : Nat := 1\n')
            actual,actual_mentions=lc.read_graph(root,config)
            self.assertEqual((graph,mentions),(actual,actual_mentions))
            # Also verify the opposite change via an explicit downstream import.
            entry['downstream_imports']={module:['Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant']}
            put(module,text);(root/(dest.replace('.','/')+'.lean')).unlink()
            second=validate(root,[entry],{module:snap},config)
            self.assertEqual(second['after']['closure']['W2a'],1)
