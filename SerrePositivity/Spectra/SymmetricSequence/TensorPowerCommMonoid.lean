module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerBraiding
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-! # 反復テンソルの対称列の可換モノイド構造

全次数のブロック交換とconvolutionの普遍性から乗法の可換性を得て、
構成済みのモノイド対象に可換性を登録する。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]

/-- convolution全体の反復テンソルの乗法の可換性。 -/
lemma tensorPower_commutativity (X : C) :
    (β_ (tensorPowerSequence X) (tensorPowerSequence X)).hom ≫
        tensorPowerMultiplication X = tensorPowerMultiplication X :=
  (tensorPower_commutativity_iff X).mpr (tensorPower_block_swap X)

/-- 既存の反復テンソルのモノイド構造に、可換性を登録する。 -/
instance tensorPowerIsCommMonObj (X : C) : IsCommMonObj (tensorPowerSequence X) where
  mul_comm := tensorPower_commutativity X

end SerrePositivity.SymmetricSequence
