"""Guards for preserving every actual binding of a plain multi-binding open."""
from pathlib import Path
from unittest import TestCase,main,mock
import copy,os,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import bulk_namespace as B
import bulk_collect as Collect

def fixture():
 source='open CategoryTheory Bicategory MonoidalClosed SSet\n';names=[['CategoryTheory'],['Bicategory','CategoryTheory.Bicategory'],['CategoryTheory.MonoidalClosed'],['SSet']];commands=[];at=5
 for word,resolved in zip(source.strip().split()[1:],names):
  commands.append(dict(kind='open',mode='simple',start=at,stop=at+len(word),names=resolved,command=dict(start=5,stop=len(source)-1)));at+=len(word)+1
 return dict(module='M',source=source,refs=[],commands=commands)
def migration(opens=None):return B.K.Migration(dict(modules={},namespaces={'M':{'Before':'After'}},rows=[],opens=opens or {}))
class PlainOpenTests(TestCase):
 def test_all_original_bindings_are_preserved_in_order(self):
  data=fixture();old,issues=B.K.rewrite(data,migration());self.assertIsNone(old);self.assertTrue(issues)
  result,issues=B.rewrite(data,migration());self.assertFalse(issues);self.assertEqual(result.decode(),'open _root_.CategoryTheory _root_.Bicategory _root_.CategoryTheory.Bicategory _root_.CategoryTheory.MonoidalClosed _root_.SSet\n')
 def test_changed_multi_binding_policy_still_requires_review(self):
  result,issues=B.rewrite(fixture(),migration({'Bicategory':'UnverifiedDestination'}));self.assertIsNone(result);self.assertTrue(issues)
 def test_removing_a_multi_binding_open_still_requires_review(self):
  result,issues=B.rewrite(fixture(),migration({'Bicategory':None}));self.assertIsNone(result);self.assertTrue(issues)
 def test_private_helper_never_changes_shared_files_and_restores_state(self):
  original=Collect.K.HERE;source=(original/'klw1_collect_refs.lean').read_bytes();calls=[]
  def failure(*args):
   private=Collect.K.HERE;self.assertNotEqual(private,original);self.assertEqual((private/'klw1_collect_refs.lean').read_text(),Collect.patched_helper(source.decode()));calls.append(private);raise RuntimeError('fixture failure')
  with mock.patch.object(Collect.K,'collect',side_effect=failure):
   with self.assertRaises(RuntimeError):Collect.collect(Path('/tmp'),[],Path('/tmp/unused-output'))
  self.assertEqual(Collect.K.HERE,original);self.assertEqual((original/'klw1_collect_refs.lean').read_bytes(),source);self.assertFalse(calls[0].exists())
 def test_changed_shared_helper_requires_a_fresh_review(self):
  with self.assertRaises(ValueError):Collect.patched_helper('changed implementation')
if __name__=='__main__':main()
