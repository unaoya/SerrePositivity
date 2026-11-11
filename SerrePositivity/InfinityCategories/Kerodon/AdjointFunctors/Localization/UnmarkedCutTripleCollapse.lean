module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardTripleDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams

/-!
# 元の内部切断の三列圧縮と同じ列の因子化

概要：接頭射・生成矢・残りの全三列を圧縮し、元の同じ列の図式を回収する。
方針：全図式の三列圧縮と元の自然変換の因子化の等式を合成する。
規約：元の両接合点の関手と全縦射を保持する。
使われ方：前後の全語へ接続した refinedDiagram の回収の局所部分。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])

def collapsedColumnDiagram := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W.paths
  (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint_eq_rowSource W τ i h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowColumn W τ i h ≫
    eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint_eq_rowTarget W τ i h).symm)
  (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).endpoint_right_mem f)
  (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i).endpoint_left_mem f)

lemma collapse_blocks :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.collapse
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock W τ i h).append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock W τ i h)).append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.rightBlock W τ i h)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.collapsedColumnDiagram W τ i h := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.rightBlock, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.collapsedColumnDiagram,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.attachment_factorization] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.collapse_diagram W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment W τ i h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGeneratorMap W τ i h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.rightAttachment W τ i h)
      (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).endpoint_right_mem f)
      (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)
      (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i).endpoint_left_mem f)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
