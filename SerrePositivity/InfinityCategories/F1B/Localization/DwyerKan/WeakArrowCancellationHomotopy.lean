module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WeakArrowUnitRows
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitRowHomotopy

/-!
# 指定射の往復を単位に結ぶ実際の単体的ホモトピー

概要：二列の縦比較を元の全語の余極限へ送る。
方針：恒等行を空語の標準射へ照合してホモトピーの端点を回収する。
規約：単体集合のモデル構造や元の指定射の逆射を要求しない。
使われ方：指定射による前後合成のホモトピー逆。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.WeakArrow
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C}

lemma colimitRowMap_sourceUnit (X : C) :
    colimitRowMap (sourceUnit (W := W) X) = colimitUnit W X := by
  rw [← empty_sourceUnit W X, colimitRowMap_wordAction, colimitRowMap_empty]

lemma colimitRowMap_targetUnit (Y : C) :
    colimitRowMap (targetUnit (W := W) Y) = colimitUnit W Y := by
  rw [← empty_targetUnit W Y, colimitRowMap_wordAction, colimitRowMap_empty]

def sourceCancellationHomotopy (g : X ⟶ Y) (hg : W g) :
    SSet.Homotopy (colimitUnit W X) (colimitRowMap (sourceRoundTrip g hg)) := by
  simpa only [colimitRowMap_sourceUnit] using colimitRowHomotopy (sourceCancellation g hg)

def targetCancellationHomotopy (g : X ⟶ Y) (hg : W g) :
    SSet.Homotopy (colimitRowMap (targetRoundTrip g hg)) (colimitUnit W Y) := by
  simpa only [colimitRowMap_targetUnit] using colimitRowHomotopy (targetCancellation g hg)

end SerrePositivity.EInfinity.Hammock.WeakArrow
