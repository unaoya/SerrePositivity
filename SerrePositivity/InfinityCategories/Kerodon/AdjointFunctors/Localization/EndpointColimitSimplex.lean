module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit

/-!
# 元の hammock 標準射の単体作用素と語・端点表示の変更

概要：全単体作用素で再添字した元の単体の標準射の像を、表示を移して回収する。
方針：語と端点の等式で帰納し、同じ元の標準射の自然性を使う。
規約：元の単体の異種等式を用い、余極限の新しい表示は選ばない。
使われ方：依存和の切断射の単体的自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X X' Y Y' : C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}

lemma image_simplex (hab : a = b) (hX : X = X') (hY : Y = Y')
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (S : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n)
    (T : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b X' Y').obj m) (hST : HEq T ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).map θ S)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit.colimitMap W hX hY).app m
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).map θ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app n S)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X' Y' b).app m T := by
  cases hab
  cases hX
  cases hY
  have hn := congrArg (fun k => k S) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).naturality θ)
  exact hn.symm.trans (congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app m z) (eq_of_heq hST).symm)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
