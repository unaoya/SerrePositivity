module

public import SerrePositivity.Spectra.SymmetricSequence.DayAssociativityComparisons
public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerUnitLaws

/-! # 反復テンソルの対称列の乗法の結合則

各次数の連結同型の結合の整合性を、convolution全体の乗法の結合則へ持ち上げる。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.FiniteBijection

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]

private lemma finCongr_trans_eq {a b c : ℕ} (h : a = b) (k : b = c) :
    (finCongr h).trans (finCongr k) = finCongr (h.trans k) := by
  subst b
  subst c
  rfl

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 添字圏の結合子の逆射の像は、次数の結合則による移送。 -/
lemma tensorPowerSequence_map_sumAssociator_inv (X : C) (l m n : ℕ) :
    (tensorPowerSequence X).map (FiniteBijection.sumAssociator
      (FiniteBijection.of l) (FiniteBijection.of m) (FiniteBijection.of n)).inv =
      eqToHom (congrArg (TensorPowers.power X) (Nat.add_assoc l m n).symm) := by
  simp [tensorPowerSequence, TensorPowers.bijectionFunctor, FiniteBijection.familyFunctor,
    FiniteBijection.familyMap, FiniteBijection.sumAssociator, FiniteBijection.isoOfEquiv,
    FiniteBijection.assocEquiv_eq_finCongr, finCongr_trans_eq, ← Equiv.Perm.one_def]

/-- 反復テンソルの対称列の、convolution全体の乗法の結合則。 -/
lemma tensorPower_associativity (X : C) :
    (tensorPowerMultiplication X ▷ tensorPowerSequence X) ≫ tensorPowerMultiplication X =
      (α_ (tensorPowerSequence X) (tensorPowerSequence X) (tensorPowerSequence X)).hom ≫
        (tensorPowerSequence X ◁ tensorPowerMultiplication X) ≫ tensorPowerMultiplication X := by
  apply convolution_triple_hom_ext (tensorPowerSequence X) (tensorPowerSequence X)
    (tensorPowerSequence X) (tensorPowerSequence X)
  intro x y z
  rw [← FiniteBijection.of_card x, ← FiniteBijection.of_card y, ← FiniteBijection.of_card z]
  erw [convolutionUnit_whiskerRight_assoc]
  erw [← comp_whiskerRight_assoc, tensorPowerMultiplication_fac_app]
  erw [tensorPowerMultiplication_fac_app]
  erw [convolution_associator_generator_assoc]
  erw [NatTrans.naturality (tensorPowerSequence X ◁ tensorPowerMultiplication X ≫
    tensorPowerMultiplication X)]
  erw [NatTrans.comp_app]
  simp only [Category.assoc]
  erw [convolutionUnit_whiskerLeft_assoc]
  erw [← whiskerLeft_comp_assoc, tensorPowerMultiplication_fac_app]
  erw [← Category.assoc _ _ ((tensorPowerSequence X).map
    (FiniteBijection.sumAssociator (of (card x)) (of (card y)) (of (card z))).inv),
    tensorPowerMultiplication_fac_app]
  rw [tensorPowerSequence_map_sumAssociator_inv]
  have h := congrArg (fun f ↦ f ≫ eqToHom (congrArg (TensorPowers.power X)
    (Nat.add_assoc (card x) (card y) (card z)).symm))
    (TensorPowers.appendIso_associativity X (card x) (card y) (card z))
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    tensorPowerSequence, TensorPowers.bijectionFunctor, FiniteBijection.familyFunctor,
    externalProductBifunctor_obj_obj, FiniteBijection.sumObj, FiniteBijection.card_of] using h
end SerrePositivity.SymmetricSequence
