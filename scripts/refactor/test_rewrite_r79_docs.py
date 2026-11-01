"""R79 exact docstring-only replacement; no Lean process."""
import unittest
from rewrite_r79_docs import rewrite,section_anchor,github_slug

class RewriteTests(unittest.TestCase):
    def test_relative_depth_anchor_and_code_preserved(self):
        source='module\n/-!\n[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m1234\n[plan]: ../../../../formalization-plans/k-theory.md\n-/\ndef keep := 1\n'
        out,edits=rewrite(source,'SerrePositivity/HomotopicalAlgebra/Test.lean','all','396-test')
        self.assertIn('../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m1234',out)
        self.assertIn('../../../../formalization-plans/archive/k-theory-v1.md#396-test',out)
        self.assertTrue(out.endswith('-/\ndef keep := 1\n'));self.assertEqual(len(edits),2)
    def test_inline_inventory_and_layout_anchor(self):
        src='/-!\n詳細はformalization-plans/k-theory-generalization-inventory.mdの配置実施記録を参照。\n[inventory]: ../../formalization-plans/k-theory-generalization-inventory.md#layout-execution\n-/\n'
        out,edits=rewrite(src,'x','inventory','unused')
        self.assertEqual([e['form'] for e in edits],['inline','reference'])
        self.assertIn('.md#layout-execution',out)
    def test_only_known_inline_plan(self):
        src='/-! `formalization-plans/k-theory.md` -/'
        with self.assertRaisesRegex(ValueError,'unreviewed'):rewrite(src,'x','plan','396')
        self.assertIn('#396',rewrite(src,'SerrePositivity/Spectra/StageTwo.lean','plan','396')[0])
    def test_string_and_ordinary_comment_not_docstring(self):
        for src in ['def s := "/-! formalization-plans/k-theory.md -/"', '/- formalization-plans/k-theory.md -/']:
            with self.assertRaisesRegex(ValueError,'outside'):rewrite(src,'x','plan','396')
    def test_nested_comment_and_crlf(self):
        src='/-!\r\n/- nested -/\r\n[plan]: ../formalization-plans/k-theory.md\r\n-/\r\n'
        out,_=rewrite(src,'x','plan','396')
        self.assertEqual(out.count('\r\n'),src.count('\r\n'))
    def test_heading_and_duplicate_slug(self):
        heading='396. 任意モデル源への一般化（中断）（2026-10-17）'
        self.assertEqual(section_anchor('## '+heading+'\n'),(heading,'396-任意モデル源への一般化中断2026-10-17'))
        self.assertEqual(github_slug('Example: _Keep-Me_!'),'example-_keep-me_')
        with self.assertRaisesRegex(ValueError,'exactly one'):section_anchor('# Missing\n')
    def test_separate_passes_same_as_combined(self):
        src='/-!\n[plan]: ../formalization-plans/k-theory.md\n[inventory]: ../formalization-plans/k-theory-generalization-inventory.md#m1\n-/\n'
        one,_=rewrite(src,'x','plan','396');two,_=rewrite(one,'x','inventory','396')
        self.assertEqual(two,rewrite(src,'x','all','396')[0])
        self.assertEqual(rewrite(two,'x','all','396')[1],[])

if __name__=='__main__':unittest.main()
