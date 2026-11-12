module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedAmbientRecovery
public import SerrePositivity.EInfinity.Hammock.AllMarkedEndpointTransport
public import SerrePositivity.EInfinity.Hammock.AllMarkedEmbedding

/-!
# 元の貼り戻しの指定 prefix の実際の点の回収

概要：元の指定部分圏の hammock 内で同じ prefix の点を回収する。
方針：包含の端点移送の可換性と単射性を元の ambient 回収式へ適用する。
規約：元の W-hammock 自身の点の一致である。
使われ方：切断の依存和の元の三因子全体の回収。
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

set_option maxHeartbeats 2000000 in
-- 元の切断の依存端点と包含の比較で大きな定義的等式を照合するため。
lemma prefix_native_point :
    let η := simplex W g σ τ
    let hg := simplex_generator W g σ τ h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit.colimitMap (⊤ : MorphismProperty (WideSubcategory W.paths)) rfl
      (congrArg (fun t : Quiver.Total C => (⟨t.left⟩ : WideSubcategory W.paths)) hg)).app n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.leftPoint W η h) = (AllMarked.nativeInclusion W X g.val.left a).app n σ := by
  dsimp only
  let η := simplex W g σ τ
  let A : Paths C := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.generator W η h).val.left
  let e : A = g.val.left := congrArg (fun t : Quiver.Total C =>
    (show Paths C from t.left)) (simplex_generator W g σ τ h)
  have he := congrArg (fun k => k.app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.leftPoint W η h))
    (AllMarked.inclusion_endpoint W (rfl : X = X) e)
  have hp := congrArg (fun k => k.app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedSimplex W η h))
    (AllMarked.nativeInclusion_inclusion W X A
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W η h)))
  have hσ := congrArg (fun k => k.app n σ)
    (AllMarked.nativeInclusion_inclusion W X g.val.left a)
  apply AllMarked.inclusion_injective W X g.val.left n
  exact he.trans ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit.colimitMap W.paths rfl e).app n) hp).trans
    ((prefix_ambient_point W g σ τ h).trans hσ.symm))

lemma factor_point : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.point W (simplex W g σ τ) h =
    (⟨g, (AllMarked.nativeInclusion W X g.val.left a).app n σ,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths g.val.right Y b).app n τ⟩ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).obj n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTargetTransport.point_ext W (simplex_generator W g σ τ h) _ _ _ _
    (prefix_native_point W g σ τ h) (residual_ambient_point W g σ τ h)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
