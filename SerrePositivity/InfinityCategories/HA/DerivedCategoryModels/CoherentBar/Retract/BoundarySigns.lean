module
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.Ring
/-!
概要：実 bar の次元符号と Dold–Kan のホモトピー符号の一致を与える。
方針：積を指数の和にまとめ、二つの指数の差が偶数であることを使う。
規約：正位置の二種類の面項と最後の段の残余を区別する。
使われ方：普遍 Hσ 係数の線形作用と実正規化境界の有限和の照合。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract

lemma dgCoherentBarBoundary_left_sign {n q a : ℕ} (hn : n = a + q) (i : ℕ) :
    ((q : ℤ) + 1).negOnePow *
      (((n + 1 : ℕ) : ℤ) + 1 + (i : ℤ) + 1).negOnePow =
    ((a + 1 : ℕ) : ℤ).negOnePow * ((i + 1 : ℕ) : ℤ).negOnePow := by
  subst n
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  refine ⟨(q : ℤ) + 1, ?_⟩
  simp only [Nat.cast_add, Nat.cast_one]
  ring

lemma dgCoherentBarBoundary_right_sign {n q a : ℕ} (hn : n = a + q) (i : ℕ) :
    ((n : ℤ) + 1 + (i : ℤ) + 1).negOnePow * ((q : ℤ) + 1).negOnePow =
    (a : ℤ).negOnePow * ((i + 1 : ℕ) : ℤ).negOnePow := by
  subst n
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  refine ⟨(q : ℤ) + 1, ?_⟩
  simp only [Nat.cast_add]
  ring

lemma dgCoherentBarBoundary_last_sign (n i : ℕ) :
    (((n + 1 : ℕ) : ℤ) + 1).negOnePow *
      (((n + 1 : ℕ) : ℤ) + 1 + ((i + 1 : ℕ) : ℤ) + 1).negOnePow =
    ((i + 2 : ℕ) : ℤ).negOnePow := by
  rw [← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  refine ⟨(n : ℤ) + 2, ?_⟩
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
