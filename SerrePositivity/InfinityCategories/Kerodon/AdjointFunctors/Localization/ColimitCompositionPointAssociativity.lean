module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionAssociativity

/-!
# 各次数の元の点の合成の結合則

概要：任意の三つの元の hammock の点に対する結合則を回収する。
方針：元の余極限上の合成の結合則を同じ点で評価する。
規約：語の表示や余極限の選択を変更しない。
使われ方：全因子列の明示的な連結と元の合成の比較。

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
  {X Y Z T : C} {n : SimplexCategoryᵒᵖ}

lemma composePoint_assoc (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).obj n)
    (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z).obj n) (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Z T).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Z T (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z p q) r =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y T p (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W Y Z T q r) :=
  congrArg (fun f => f.app n ((p, q), r)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_assoc W X Y Z T)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
