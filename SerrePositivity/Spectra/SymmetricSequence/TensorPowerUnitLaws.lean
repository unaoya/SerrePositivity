module

public import SerrePositivity.Spectra.SymmetricSequence.DayUnitComparisons
public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerUnit

/-! # 反復テンソルの対称列の左右単位則

二段のKan拡張の普遍性を用い、標準射上の単位比較をconvolution全体の単位則へ持ち上げる。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]

private lemma finCongr_trans_eq {a b c : ℕ} (h : a = b) (k : b = c) :
    (finCongr h).trans (finCongr k) = finCongr (h.trans k) := by
  subst b
  subst c
  rfl

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 直和の左単位同型の逆射の像は、次数の移送。 -/
lemma tensorPowerSequence_map_sumLeftUnitor_inv (X : C) (n : ℕ) :
    (tensorPowerSequence X).map (FiniteBijection.sumLeftUnitor (FiniteBijection.of n)).inv =
      eqToHom (congrArg (TensorPowers.power X) (Nat.zero_add n).symm) := by
  simp [tensorPowerSequence, TensorPowers.bijectionFunctor, FiniteBijection.familyFunctor,
    FiniteBijection.familyMap, FiniteBijection.sumLeftUnitor, FiniteBijection.isoOfEquiv,
    finCongr_trans_eq, ← Equiv.Perm.one_def, TensorPowers.permutationAction_one]

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 直和の右単位同型の逆射の像は恒等射。 -/
lemma tensorPowerSequence_map_sumRightUnitor_inv (X : C) (n : ℕ) :
    (tensorPowerSequence X).map (FiniteBijection.sumRightUnitor (FiniteBijection.of n)).inv =
      𝟙 (TensorPowers.power X n) := by
  simp [tensorPowerSequence, TensorPowers.bijectionFunctor, FiniteBijection.familyFunctor,
    FiniteBijection.familyMap, FiniteBijection.sumRightUnitor, FiniteBijection.isoOfEquiv,
    ← Equiv.Perm.one_def, TensorPowers.permutationAction_one]

/-- 登録済みconvolutionの左単位則。 -/
lemma tensorPower_left_unit (X : C) :
    (tensorPowerUnitHom X ▷ tensorPowerSequence X) ≫ tensorPowerMultiplication X =
      (λ_ (tensorPowerSequence X)).hom := by
  apply convolution_left_unit_hom_ext (tensorPowerSequence X) (tensorPowerSequence X)
  intro y
  rw [← FiniteBijection.of_card y]
  erw [convolutionUnit_whiskerRight_assoc, convolution_leftUnitor_generator]
  rw [tensorPowerSequence_map_sumLeftUnitor_inv]
  exact tensorPowerUnit_left_generator X (FiniteBijection.card y)

/-- 登録済みconvolutionの右単位則。 -/
lemma tensorPower_right_unit (X : C) :
    (tensorPowerSequence X ◁ tensorPowerUnitHom X) ≫ tensorPowerMultiplication X =
      (ρ_ (tensorPowerSequence X)).hom := by
  apply convolution_right_unit_hom_ext (tensorPowerSequence X) (tensorPowerSequence X)
  intro y
  rw [← FiniteBijection.of_card y]
  erw [convolutionUnit_whiskerLeft_assoc, convolution_rightUnitor_generator]
  rw [tensorPowerSequence_map_sumRightUnitor_inv]
  erw [Category.comp_id]
  exact tensorPowerUnit_right_generator X (FiniteBijection.card y)
end SerrePositivity.SymmetricSequence
