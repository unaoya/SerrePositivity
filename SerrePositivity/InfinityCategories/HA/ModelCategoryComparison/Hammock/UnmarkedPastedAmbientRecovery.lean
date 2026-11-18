module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedPastedIdentityFunctors
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimitHEq
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitIdentityPoint

/-!
# 元の貼り戻しの二因子の ambient hammock の点の回収

概要：切断した prefix と残りの標準射の像を元の二点へ回収する。
方針：全関手の異種等式を同じ標準射へ渡し、元の合成単位則を使う。
規約：語の値だけでなく実際の全語の余極限の点を回収する。
使われ方：指定部分圏での prefix の反映と逆向きの因子回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
  (σ : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths b g.val.right Y).obj n)
  (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.simplex W g σ τ).obj 0) j ≠ [])

lemma prefix_ambient_point :
    let η := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.simplex W g σ τ
    let i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W η h
    let A : Paths C := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.generator W η h).val.left
    let e : A = g.val.left := congrArg (fun t : Quiver.Total C =>
      (show Paths C from t.left)) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.simplex_generator W g σ τ h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit.colimitMap W.paths rfl e).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord _ i)).app n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixFunctor W η i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X g.val.left a).app n
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.graphMap W X g.val.left a).app n σ) := by
  dsimp only
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.image_heq W.paths (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.selected_prefix_word W g σ τ h) rfl _ _ _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.prefix_identity_functor W g σ τ h)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions W.paths X g.val.left g.val.left a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.graphMap W X g.val.left a).app n σ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W.paths (𝟙 (show Paths C from g.val.left)) n)).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_identity_right W.paths _))

lemma residual_ambient_point :
    let η := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.simplex W g σ τ
    let i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W η h
    let B : Paths C := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.generator W η h).val.right
    let e : B = g.val.right := congrArg (fun t : Quiver.Total C =>
      (show Paths C from t.right)) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.simplex_generator W g σ τ h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit.colimitMap W.paths e rfl).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths B Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord _ i)).app n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualFunctor W η i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths g.val.right Y b).app n τ := by
  dsimp only
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.image_heq W.paths (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.selected_residual_word W g σ τ h) _ rfl _ _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.residual_identity_functor W g σ τ h)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions W.paths g.val.right g.val.right Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) b
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W.paths (𝟙 (show Paths C from g.val.right)) n) τ).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_identity_left W.paths _))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted
