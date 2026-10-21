module

public import SerrePositivity.EInfinity.Hammock.ForwardTripleDiagram
public import SerrePositivity.EInfinity.Hammock.UnmarkedCutAttachmentDiagrams

/-!
# 元の内部切断の三列圧縮と同じ列の因子化

概要：接頭射・生成矢・残りの全三列を圧縮し、元の同じ列の図式を回収する。
方針：全図式の三列圧縮と元の自然変換の因子化の等式を合成する。
規約：元の両接合点の関手と全縦射を保持する。
使われ方：前後の全語へ接続した refinedDiagram の回収の局所部分。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ [])

def collapsedColumnDiagram := ForwardZigzag.diagram W.paths
  (eqToHom (sourceJoint_eq_rowSource W τ i h) ≫ rowColumn W τ i h ≫
    eqToHom (targetJoint_eq_rowTarget W τ i h).symm)
  (fun f => (beforeDiagram W τ i).endpoint_right_mem f)
  (fun f => (afterDiagram W τ i).endpoint_left_mem f)

lemma collapse_blocks :
    Zigzag.MovingDiagram.wordAction Word.ForwardTriple.collapse
      (((leftBlock W τ i h).append (generatorBlock W τ i h)).append (rightBlock W τ i h)) =
      collapsedColumnDiagram W τ i h := by
  simpa only [leftBlock, generatorBlock, rightBlock, collapsedColumnDiagram,
    attachment_factorization] using
    ForwardTriple.collapse_diagram W.paths (leftAttachment W τ i h)
      (rowGeneratorMap W τ i h) (rightAttachment W τ i h)
      (fun f => (beforeDiagram W τ i).endpoint_right_mem f)
      (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)
      (fun f => (afterDiagram W τ i).endpoint_left_mem f)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
