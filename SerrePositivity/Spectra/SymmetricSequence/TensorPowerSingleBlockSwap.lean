module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerCommutativity
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Blocks

/-! # 第1段と任意の段のブロック交換

巡回置換の既存の作用と右単位子を用いて、第1段と任意の段の連結をbraidingと比較する。
一般の二つの正次数のブロック全体の交換はまだ含まない。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open SerrePositivity.FiniteBijection SerrePositivity.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

private lemma finCongr_trans_eq {a b c : ℕ} (h : a = b) (k : b = c) :
    (finCongr h).trans (finCongr k) = finCongr (h.trans k) := by
  subst b
  subst c
  rfl

/-- 第1段が右側にある添字のブロック交換の像は、巡回置換の作用と次数の移送。 -/
lemma tensorPowerSequence_map_swap_right_one (X : C) (n : ℕ) :
    (SymmetricSequence.tensorPowerSequence X).map (sumSymmetry (of n) (of 1)).hom =
      (permutationAction X (n + 1) (finRotate (n + 1))).asIso.hom ≫
        eqToHom (congrArg (power X) (Nat.one_add n).symm) := by
  simp [SymmetricSequence.tensorPowerSequence, bijectionFunctor, familyFunctor, familyMap,
    sumSymmetry, isoOfEquiv, FiniteBijection.swapEquiv_right_one, Equiv.trans_assoc,
    finCongr_trans_eq]
  rfl

/-- 第1段を左側に置くブロック全体の交換と連結の両立。 -/
lemma tensorPower_swap_one_left (X : C) (n : ℕ) :
    (β_ (power X 1) (power X n)).hom ≫ (appendIso X n 1).hom ≫
        (SymmetricSequence.tensorPowerSequence X).map (sumSymmetry (of n) (of 1)).hom =
      (appendIso X 1 n).hom := by
  rw [tensorPowerSequence_map_swap_right_one, TensorPowers.permutationAction_rotate]
  erw [TensorPowers.oneCrossing_comparison_assoc, Iso.hom_inv_id_assoc]
  exact (appendIso_one_left X n).symm

/-- 第1段を右側に置くブロック全体の交換と連結の両立。 -/
lemma tensorPower_swap_one_right (X : C) (n : ℕ) :
    (β_ (power X n) (power X 1)).hom ≫ (appendIso X 1 n).hom ≫
        (SymmetricSequence.tensorPowerSequence X).map (sumSymmetry (of 1) (of n)).hom =
      (appendIso X n 1).hom := by
  rw [← tensorPower_swap_one_left X n]
  simp only [Category.assoc]
  rw [SymmetricCategory.symmetry_assoc]
  erw [← CategoryTheory.Functor.map_comp, sumSymmetry_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end SerrePositivity.SymmetricSequence
