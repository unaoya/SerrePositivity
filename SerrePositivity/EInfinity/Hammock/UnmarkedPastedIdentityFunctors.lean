module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedIdentityDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagConstantDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFixedAppendFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitFunctor

/-!
# 元の切断因子の関手と恒等列付き元の関手の比較

概要：固定した全端点の実際の prefix・残りの関手を回収する。
方針：元の全図式の比較を fixedFunctor へ移し、一列の一定関手を照合する。
規約：元の選択生成矢の端点の表示変更を保持する。
使われ方：同じ元の標準射による二因子の余極限の点の回収。
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

lemma selected_prefix_word :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) :=
  (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b))
    (simplex_firstColumn W g σ τ h)).trans (prefix_word a b)

lemma selected_residual_word :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) b :=
  (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b))
    (simplex_firstColumn W g σ τ h)).trans (residual_word a b)

lemma prefix_identity_functor :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixFunctor W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h))
      ((((AllMarked.graphMap W X g.val.left a).app n σ).prod'
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W.paths (𝟙 (show Paths C from g.val.left)) n)) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor) := by
  have hg := congrArg (fun t : Quiver.Total C => (show Paths C from t.left))
    (simplex_generator W g σ τ h)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_heq (selected_prefix_word W g σ τ h) rfl hg _ _
    (prefix_identity_diagram W g σ τ h)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_fixedFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor_fixedFunctor,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.identity_diagram_fixedFunctor] at he
  exact he

lemma residual_identity_functor :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualFunctor W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W.paths (𝟙 (show Paths C from g.val.right)) n).prod' τ ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor) := by
  have hg := congrArg (fun t : Quiver.Total C => (show Paths C from t.right))
    (simplex_generator W g σ τ h)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_heq (selected_residual_word W g σ τ h) hg rfl _ _
    (residual_identity_diagram W g σ τ h)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_fixedFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor_fixedFunctor,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.identity_diagram_fixedFunctor] at he
  exact he

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
