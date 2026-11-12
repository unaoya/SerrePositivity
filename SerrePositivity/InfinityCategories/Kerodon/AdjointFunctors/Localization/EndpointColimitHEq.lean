module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit

/-!
# 語と端点表示の異種等式からの元の標準射の回収

概要：全関手が異種等式で一致すれば、元の標準射の像は端点移送で一致する。
方針：語と端点の等式を消去して元の同じ標準射を使う。
規約：余極限の新しい表示を選ばない。
使われ方：元の切断因子の点を元の prefix・残りへ回収する。

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
  {X X' Y Y' : C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {n : SimplexCategoryᵒᵖ}

lemma image_heq (hw : a = b) (hX : X = X') (hY : Y = Y')
    (S : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n) (T : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b X' Y').obj n) (hST : HEq S T) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit.colimitMap W hX hY).app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app n S) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X' Y' b).app n T := by
  cases hw
  cases hX
  cases hY
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app n S = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app n T
  exact congrArg (fun F => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app n F) (eq_of_heq hST)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
