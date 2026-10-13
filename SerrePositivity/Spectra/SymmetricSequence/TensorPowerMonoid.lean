module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerAssociativity
public import Mathlib.CategoryTheory.Monoidal.Mon

/-! # 反復テンソルの対称列のモノイド構造

convolution上の乗法・単位射と、結合則・左右単位則をモノイド対象として登録する。
可換性はまだ登録しない。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]

/-- 反復テンソルの対称列に、構成済みの乗法と単位を持つモノイド構造を登録する。 -/
instance tensorPowerMonObj (X : C) : MonObj (tensorPowerSequence X) where
  one := tensorPowerUnitHom X
  mul := tensorPowerMultiplication X
  one_mul := tensorPower_left_unit X
  mul_one := tensorPower_right_unit X
  mul_assoc := tensorPower_associativity X

/-- モノイド構造の単位射は既存の単位射。 -/
lemma tensorPowerMonObj_one (X : C) :
    MonObj.one (X := tensorPowerSequence X) = tensorPowerUnitHom X := rfl

/-- モノイド構造の乗法は既存の乗法。 -/
lemma tensorPowerMonObj_mul (X : C) :
    MonObj.mul (X := tensorPowerSequence X) = tensorPowerMultiplication X := rfl

end SerrePositivity.SymmetricSequence
