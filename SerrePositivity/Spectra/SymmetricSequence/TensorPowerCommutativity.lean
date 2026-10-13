module

public import SerrePositivity.Spectra.SymmetricSequence.DayBraidingComparisons
public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerMonoid

/-! # 反復テンソルの乗法の可換性の帰着

可換性の必要十分条件を各次数のブロック全体の交換として述べ、第0段を含む場合を証明する。
正次数どうしのブロック交換は `TensorPowerBraiding`、可換性全体は `TensorPowerCommMonoid` で証明する。
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

/-- 反復テンソルの乗法の可換性は、各次数の連結とブロック全体の交換の両立と同値。 -/
lemma tensorPower_commutativity_iff (X : C) :
    (β_ (tensorPowerSequence X) (tensorPowerSequence X)).hom ≫
        tensorPowerMultiplication X = tensorPowerMultiplication X ↔
      ∀ m n : ℕ,
        (β_ (TensorPowers.power X m) (TensorPowers.power X n)).hom ≫
          (TensorPowers.appendIso X n m).hom ≫
          (tensorPowerSequence X).map
            (FiniteBijection.sumSymmetry (FiniteBijection.of n) (FiniteBijection.of m)).hom =
        (TensorPowers.appendIso X m n).hom := by
  rw [convolution_commutativity_iff]
  constructor
  · intro h m n
    have hh := h (FiniteBijection.of m) (FiniteBijection.of n)
    erw [← Category.assoc _ _ ((tensorPowerSequence X).map
      (FiniteBijection.sumSymmetry (FiniteBijection.of n) (FiniteBijection.of m)).hom),
      tensorPowerMultiplication_fac_app, tensorPowerMultiplication_fac_app] at hh
    exact hh
  · intro h x y
    rw [← FiniteBijection.of_card x, ← FiniteBijection.of_card y]
    erw [← Category.assoc _ _ ((tensorPowerSequence X).map
      (FiniteBijection.sumSymmetry (FiniteBijection.of (FiniteBijection.card y))
        (FiniteBijection.of (FiniteBijection.card x))).hom),
      tensorPowerMultiplication_fac_app, tensorPowerMultiplication_fac_app]
    exact h (FiniteBijection.card x) (FiniteBijection.card y)

private lemma finCongr_trans_eq {a b c : ℕ} (h : a = b) (k : b = c) :
    (finCongr h).trans (finCongr k) = finCongr (h.trans k) := by
  subst b
  subst c
  rfl

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 空の右ブロックの交換の像は、次数の移送。 -/
lemma tensorPowerSequence_map_swap_zero_right (X : C) (n : ℕ) :
    (tensorPowerSequence X).map (FiniteBijection.sumSymmetry (of n) (of 0)).hom =
      eqToHom (congrArg (TensorPowers.power X) (Nat.zero_add n).symm) := by
  simp [tensorPowerSequence, TensorPowers.bijectionFunctor, FiniteBijection.familyFunctor,
    FiniteBijection.familyMap, FiniteBijection.sumSymmetry, FiniteBijection.isoOfEquiv,
    FiniteBijection.swapEquiv_zero_right, finCongr_trans_eq, ← Equiv.Perm.one_def]

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 空の左ブロックの交換の像は、次数の移送。 -/
lemma tensorPowerSequence_map_swap_zero_left (X : C) (n : ℕ) :
    (tensorPowerSequence X).map (FiniteBijection.sumSymmetry (of 0) (of n)).hom =
      eqToHom (congrArg (TensorPowers.power X) (Nat.zero_add n)) := by
  simp [tensorPowerSequence, TensorPowers.bijectionFunctor, FiniteBijection.familyFunctor,
    FiniteBijection.familyMap, FiniteBijection.sumSymmetry, FiniteBijection.isoOfEquiv,
    FiniteBijection.swapEquiv_zero_left, finCongr_trans_eq, ← Equiv.Perm.one_def]

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 第0段を左側に置く場合のブロック全体の交換と連結の両立。 -/
lemma tensorPower_swap_zero_left (X : C) (n : ℕ) :
    (β_ (TensorPowers.power X 0) (TensorPowers.power X n)).hom ≫
        (TensorPowers.appendIso X n 0).hom ≫
        (tensorPowerSequence X).map (FiniteBijection.sumSymmetry (of n) (of 0)).hom =
      (TensorPowers.appendIso X 0 n).hom := by
  rw [TensorPowers.appendIso_zero_right, TensorPowers.appendIso_zero_left,
    tensorPowerSequence_map_swap_zero_right]
  exact braiding_rightUnitor_assoc _ _

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 第0段を右側に置く場合のブロック全体の交換と連結の両立。 -/
lemma tensorPower_swap_zero_right (X : C) (n : ℕ) :
    (β_ (TensorPowers.power X n) (TensorPowers.power X 0)).hom ≫
        (TensorPowers.appendIso X 0 n).hom ≫
        (tensorPowerSequence X).map (FiniteBijection.sumSymmetry (of 0) (of n)).hom =
      (TensorPowers.appendIso X n 0).hom := by
  rw [TensorPowers.appendIso_zero_right, TensorPowers.appendIso_zero_left,
    tensorPowerSequence_map_swap_zero_left]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact braiding_leftUnitor _
/-- 可換性を正次数どうしのブロック交換だけへ帰着する。第0段の比較は証明済み。 -/
lemma tensorPower_commutativity_iff_positive (X : C) :
    (β_ (tensorPowerSequence X) (tensorPowerSequence X)).hom ≫
        tensorPowerMultiplication X = tensorPowerMultiplication X ↔
      ∀ m n : ℕ,
        (β_ (TensorPowers.power X (m + 1)) (TensorPowers.power X (n + 1))).hom ≫
          (TensorPowers.appendIso X (n + 1) (m + 1)).hom ≫
          (tensorPowerSequence X).map
            (FiniteBijection.sumSymmetry (of (n + 1)) (of (m + 1))).hom =
        (TensorPowers.appendIso X (m + 1) (n + 1)).hom := by
  rw [tensorPower_commutativity_iff]
  constructor
  · intro h m n
    exact h (m + 1) (n + 1)
  · intro h m n
    cases m with
    | zero => exact tensorPower_swap_zero_left X n
    | succ m =>
      cases n with
      | zero => exact tensorPower_swap_zero_right X (m + 1)
      | succ n => exact h m n
end SerrePositivity.SymmetricSequence
