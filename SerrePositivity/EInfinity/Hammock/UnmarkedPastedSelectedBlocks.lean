module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedBlockDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingWordActionLaws

/-!
# 元の貼り戻しの選択位置での前後の全図式の回収

概要：最初の非指定列で切った前後の図式を元の二つの図式へ照合する。
方針：元の最小位置の等式と語の表示変更の異種等式を結合する。
規約：元の接合点関手と全縦射を保持する。
使われ方：恒等列付き prefix・残りの元の図式の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
  (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths b g.val.right Y).obj n)
  (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((simplex W g σ τ).obj 0) j ≠ [])

lemma selected_sourceJoint_eq :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) =
        (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from g.val.left) :=
  (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint W (simplex W g σ τ))
    (simplex_firstColumn W g σ τ h)).trans (sourceJoint_eq W g σ τ)

lemma selected_targetJoint_eq :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) =
        (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from g.val.right) :=
  (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint W (simplex W g σ τ))
    (simplex_firstColumn W g σ τ h)).trans (targetJoint_eq W g σ τ)

lemma selected_before_diagram :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor ((AllMarked.graphMap W X g.val.left a).app n σ)) := by
  have he : ∀ i, i = columnIndex a b →
      HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W (simplex W g σ τ) i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W (simplex W g σ τ) (columnIndex a b)) := by
    intro i hi
    cases hi
    rfl
  exact (he _ (simplex_firstColumn W g σ τ h)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_heq (before_word a b) _).symm.trans
      (before_diagram W g σ τ))

lemma selected_after_diagram :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ) := by
  have he : ∀ i, i = columnIndex a b →
      HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W (simplex W g σ τ) i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W (simplex W g σ τ) (columnIndex a b)) := by
    intro i hi
    cases hi
    rfl
  exact (he _ (simplex_firstColumn W g σ τ h)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_heq (after_word a b) _).symm.trans
      (after_diagram W g σ τ))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
