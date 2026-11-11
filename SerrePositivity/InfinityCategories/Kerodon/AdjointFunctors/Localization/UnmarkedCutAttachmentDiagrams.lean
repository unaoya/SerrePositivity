module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments

/-!
# 内部の切断を前後の全語へ貼った prefix と残り

概要：指定接頭射と残りの射を一列の図式にし、元の前後の全語に接続する。
方針：接合点関手を共有して MovingDiagram.append を適用する。
規約：元の全縦射と両端の固定対象を保持する。
使われ方：指定 prefix の W-hammock への回収と全体の貼り戻し。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])

lemma eqToHom_mem {P Q : Paths C} (e : P = Q) : W.paths (eqToHom e) := by
  cases e
  exact W.paths.id_mem _

lemma leftAttachment_mem (k : Fin (n.unop.len + 1)) : W.paths ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment W τ i h).app k) := by
  change W.paths ((eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint_eq_rowSource W τ i h)).app k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix W τ i h).app k)
  rw [eqToHom_app]
  exact W.paths.comp_mem _ _ (eqToHom_mem W _) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix_mem W τ i h k)

def leftBlock := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment W τ i h)
  (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).endpoint_right_mem f) (fun _ => W.paths.id_mem _)

def rightBlock := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.rightAttachment W τ i h)
  (fun _ => W.paths.id_mem _) (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i).endpoint_left_mem f)

def generatorBlock := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGeneratorMap W τ i h)
  (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)

def prefixDiagram := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock W τ i h)

def residualDiagram := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.rightBlock W τ i h).append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i)

def refinedDiagram :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).append (generatorBlock W τ i h)).append (residualDiagram W τ i h)

def refinedFunctor := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedDiagram W τ i h).fixedFunctor

def prefixFunctor := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).fixedFunctor

def residualFunctor := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).fixedFunctor

lemma leftBlock_arrow_mem (k : Fin (n.unop.len + 1)) (j : Fin 1) :
    W.paths (((leftBlock W τ i h).obj k).arrow j) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram_arrow_mem W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment W τ i h)
    (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).endpoint_right_mem f) (fun _ => W.paths.id_mem _)
    (leftAttachment_mem W τ i h) k j

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams
