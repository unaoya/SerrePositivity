module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WeakArrowUnitRows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowHomotopy

/-!
# 指定射の往復を単位に結ぶ実際の単体的ホモトピー

概要：二列の縦比較を元の全語の余極限へ送る。
方針：恒等行を空語の標準射へ照合してホモトピーの端点を回収する。
規約：単体集合のモデル構造や元の指定射の逆射を要求しない。
使われ方：指定射による前後合成のホモトピー逆。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C}

lemma colimitRowMap_sourceUnit (X : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceUnit (W := W) X) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty_sourceUnit W X, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap_wordAction, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap_empty]

lemma colimitRowMap_targetUnit (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetUnit (W := W) Y) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W Y := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty_targetUnit W Y, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap_wordAction, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap_empty]

def sourceCancellationHomotopy (g : X ⟶ Y) (hg : W g) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceRoundTrip g hg)) := by
  simpa only [colimitRowMap_sourceUnit] using _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceCancellation g hg)

def targetCancellationHomotopy (g : X ⟶ Y) (hg : W g) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetRoundTrip g hg)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W Y) := by
  simpa only [colimitRowMap_targetUnit] using _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetCancellation g hg)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
