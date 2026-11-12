"""Negative guards for the B2 source projection around unchanged v3b hashes."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import bulk_compare as B

def fixture():
 row=dict(name='N.f',parent='N.f',module='M',kind='def',type_hash='17',body_hash='23',axioms=[],attributes={},reference_kind='named')
 return dict(schema_version=2,hash_algorithm='normalized Expr DAG mixHash proof-irrelevant v3b (term-level, proof marker)',name_map={},proof_irrelevant=True,declarations=[row],sources=[dict(module='M',source='namespace N\nprivate def f : Nat := 0\nend N\n')])

class ProjectionChecks(unittest.TestCase):
 def test_metadata_source_projection_preserves_fingerprints(self):
  a=fixture();b=copy.deepcopy(a);b['sources'][0]['source']+='attribute [cite BS19 "Lemma 2.1"] _root_.N.f\n'
  self.assertEqual(B.C.compare(a,b)['status'],'PASS')
 def test_private_body_type_axioms_and_attributes_remain_checked(self):
  for field,value in [('body_hash','24'),('type_hash','18'),('axioms',['Synthetic.axiom']),('attributes',{'simp':True})]:
   with self.subTest(field=field):
    a=fixture();b=copy.deepcopy(a);b['declarations'][0][field]=value;self.assertEqual(B.C.compare(a,b)['status'],'FAIL')
 def test_authored_quoted_auxiliary_is_not_hidden(self):
  B.projection('public def «_aux_M___macroRules_explicit» : Nat := 0\n')
  self.assertFalse(B.aux('N.«_aux_M___macroRules_explicit»','M'))
 def test_other_module_auxiliary_is_not_hidden(self):
  self.assertFalse(B.aux('N.«_aux_Other___macroRules_generated»','M'))
 def test_projection_preserves_offsets(self):
  s='namespace N\nlocal notation "x" => 1\nprivate def f : Nat := x\nend N\n'
  projected=B.projection(s);self.assertEqual(len(s),len(projected));self.assertEqual([i for i,c in enumerate(s) if c=='\n'],[i for i,c in enumerate(projected) if c=='\n'])
 def test_cli_failure_exit_status_is_not_lost(self):
  with tempfile.TemporaryDirectory() as t:
   root=Path(t);a=fixture();b=copy.deepcopy(a);b['declarations'][0]['body_hash']='24'
   for name,data in [('a',a),('b',b)]: (root/(name+'.json')).write_text(json.dumps(data))
   r=subprocess.run([sys.executable,str(Path(B.__file__)),str(root/'a.json'),str(root/'b.json'),'--output',str(root/'report.json')],text=True,capture_output=True)
   self.assertEqual(r.returncode,1,r.stderr);self.assertEqual(json.loads((root/'report.json').read_text())['status'],'FAIL');self.assertLess(len(r.stdout),500)
if __name__=='__main__':unittest.main()
