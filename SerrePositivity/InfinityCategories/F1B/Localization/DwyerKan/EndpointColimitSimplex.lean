module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.EndpointColimit

/-!
# 元の hammock 標準射の単体作用素と語・端点表示の変更

概要：全単体作用素で再添字した元の単体の標準射の像を、表示を移して回収する。
方針：語と端点の等式で帰納し、同じ元の標準射の自然性を使う。
規約：元の単体の異種等式を用い、余極限の新しい表示は選ばない。
使われ方：依存和の切断射の単体的自然性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.EndpointChange
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X X' Y Y' : C} {a b : Word}

lemma image_simplex (hab : a = b) (hX : X = X') (hY : Y = Y')
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (S : (graph W a X Y).obj n)
    (T : (graph W b X' Y').obj m) (hST : HEq T ((graph W a X Y).map θ S)) :
    (colimitMap W hX hY).app m
      ((colimitGraph W X Y).map θ ((graphInclusion W X Y a).app n S)) =
      (graphInclusion W X' Y' b).app m T := by
  cases hab
  cases hX
  cases hY
  have hn := congrArg (fun k => k S) ((graphInclusion W X Y a).naturality θ)
  exact hn.symm.trans (congrArg (fun z => (graphInclusion W X Y a).app m z) (eq_of_heq hST).symm)

end SerrePositivity.EInfinity.Hammock.EndpointChange
