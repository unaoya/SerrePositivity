module

public import SerrePositivity.Asymptotic.NormalizedLimit
public import SerrePositivity.LengthAlgebra.Core
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# 加群列の長さと Serre 条件の数値部分

短完全列の族に対して、通常の `O(s)`・`o(s)` 条件と正規化超極限が零である条件を扱う。
長さは有限性を確認してから実数化する。加法性と非負性から、中央が零評価であることと
両端が零評価であることの同値を証明する。これは長さの商の Serre 条件に使う数値部分であり、
Serre 商圏そのものの構成とは区別する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open Filter Asymptotics

/-- 非負の列の項ごとの不等式は `O` 評価を与える。 -/
lemma isBigO_of_nonneg_le {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hfg : ∀ n, f n ≤ g n) :
    f =O[atTop] g :=
  IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ by
    rw [one_mul, Real.norm_of_nonneg (hf n), Real.norm_of_nonneg ((hf n).trans (hfg n))]
    exact hfg n)

/-- 非負の列の和が `O(s)` であることと、各列が `O(s)` であることは同値。 -/
lemma nonneg_add_isBigO_iff {f g s : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (fun n ↦ f n + g n) =O[atTop] s ↔ f =O[atTop] s ∧ g =O[atTop] s := by
  constructor
  · intro h
    exact ⟨(isBigO_of_nonneg_le hf (fun n ↦ le_add_of_nonneg_right (hg n))).trans h,
      (isBigO_of_nonneg_le hg (fun n ↦ le_add_of_nonneg_left (hf n))).trans h⟩
  · rintro ⟨h₁, h₂⟩
    exact h₁.add h₂

/-- 非負の列の和が通常の `o(s)` であることと、各列が `o(s)` であることは同値。 -/
lemma nonneg_add_isLittleO_iff {f g s : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (fun n ↦ f n + g n) =o[atTop] s ↔ f =o[atTop] s ∧ g =o[atTop] s := by
  constructor
  · intro h
    exact ⟨(isBigO_of_nonneg_le hf (fun n ↦ le_add_of_nonneg_right (hg n))).trans_isLittleO h,
      (isBigO_of_nonneg_le hg (fun n ↦ le_add_of_nonneg_left (hf n))).trans_isLittleO h⟩
  · rintro ⟨h₁, h₂⟩
    exact h₁.add h₂

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
  (M N P : ℕ → ModuleCat.{u} R) (f : ∀ n, M n →ₗ[R] N n) (g : ∀ n, N n →ₗ[R] P n)
  (hf : ∀ n, Function.Injective (f n)) (hg : ∀ n, Function.Surjective (g n))
  (hex : ∀ n, Function.Exact (f n) (g n)) (htors : ∀ n, IsPowTorsion J (N n))
  (hfin : ∀ n, lam.len (N n) ≠ ⊤)

include hf hg hex htors hfin in
/-- 有限長の短完全列の族について、長さの実数化は項ごとに加法的である。 -/
lemma lengthFamily_toReal_add (n : ℕ) :
    (lam.len (N n)).toReal = (lam.len (M n)).toReal + (lam.len (P n)).toReal := by
  have h := lam.len_add_of_exact _ _ _ (f n) (g n) (hf n) (hg n) (hex n) (htors n)
  have hM := ne_top_of_le_ne_top (hfin n) (lam.len_le_of_injective (f n) (hf n) (htors n))
  have hP := ne_top_of_le_ne_top (hfin n) (lam.len_le_of_surjective (g n) (hg n) (htors n))
  rw [h, ENNReal.toReal_add hM hP]

include hf hg hex htors hfin in
/-- 短完全列の族の中央の長さが `O(s)` であることは、両端の同じ条件と同値。 -/
lemma lengthFamily_isBigO_iff (s : ℕ → ℝ) :
    (fun n ↦ (lam.len (N n)).toReal) =O[atTop] s ↔
      (fun n ↦ (lam.len (M n)).toReal) =O[atTop] s ∧
      (fun n ↦ (lam.len (P n)).toReal) =O[atTop] s := by
  simp_rw [lengthFamily_toReal_add lam M N P f g hf hg hex htors hfin]
  exact nonneg_add_isBigO_iff (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)

include hf hg hex htors hfin in
/-- 短完全列の族における通常の `o(s)` 条件は Serre 条件を満たす。 -/
lemma lengthFamily_isLittleO_iff (s : ℕ → ℝ) :
    (fun n ↦ (lam.len (N n)).toReal) =o[atTop] s ↔
      (fun n ↦ (lam.len (M n)).toReal) =o[atTop] s ∧
      (fun n ↦ (lam.len (P n)).toReal) =o[atTop] s := by
  simp_rw [lengthFamily_toReal_add lam M N P f g hf hg hex htors hfin]
  exact nonneg_add_isLittleO_iff (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)

include hf hg hex htors hfin in
/-- 短完全列の族の長さに正規化超極限を施しても加法性が保たれる。 -/
lemma lengthFamily_normalizedLimit_add (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (hN : (fun n ↦ (lam.len (N n)).toReal) =O[atTop] (fun n ↦ (s n : ℝ))) :
    normalizedLimit U s (fun n ↦ (lam.len (N n)).toReal) =
      normalizedLimit U s (fun n ↦ (lam.len (M n)).toReal) +
      normalizedLimit U s (fun n ↦ (lam.len (P n)).toReal) := by
  obtain ⟨hM, hP⟩ := (lengthFamily_isBigO_iff lam M N P f g hf hg hex htors hfin _).1 hN
  simp_rw [lengthFamily_toReal_add lam M N P f g hf hg hex htors hfin]
  exact normalizedLimit_add U hU s hs _ _ hM hP

include hf hg hex htors hfin in
/-- 正規化超極限が零となる条件は、短完全列の族に対して Serre 条件を満たす。 -/
lemma lengthFamily_normalizedLimit_zero_iff (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (hN : (fun n ↦ (lam.len (N n)).toReal) =O[atTop] (fun n ↦ (s n : ℝ))) :
    normalizedLimit U s (fun n ↦ (lam.len (N n)).toReal) = 0 ↔
      normalizedLimit U s (fun n ↦ (lam.len (M n)).toReal) = 0 ∧
      normalizedLimit U s (fun n ↦ (lam.len (P n)).toReal) = 0 := by
  rw [lengthFamily_normalizedLimit_add lam M N P f g hf hg hex htors hfin U hU s hs hN]
  obtain ⟨hM, hP⟩ := (lengthFamily_isBigO_iff lam M N P f g hf hg hex htors hfin _).1 hN
  have h₁ := normalizedLimit_nonneg U hU s hs _ hM
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
  have h₃ := normalizedLimit_nonneg U hU s hs _ hP
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
  exact add_eq_zero_iff_of_nonneg h₁ h₃

end SerrePositivity.Asymptotic
