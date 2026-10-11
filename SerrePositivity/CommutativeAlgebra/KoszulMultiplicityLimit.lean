module

public import SerrePositivity.CommutativeAlgebra.MultiplicityFormulas
public import SerrePositivity.CommutativeAlgebra.KoszulFiniteLength
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Algebra.BigOperators.Field

/-! # Koszul ホモロジーの消滅極限と重複度

パラメータ系の冪についての Euler 公式は、既存の重複度公式から導く。
高次ホモロジーの正規化長さが零へ収束すれば、零次の商の正規化長さは
Hilbert–Samuel 重複度へ収束する。高次の消滅極限自体とは区別する。
-/

public section

universe u

namespace SerrePositivity.HilbertSamuel

open IsLocalRing CategoryTheory Filter
open scoped ENNReal

variable (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]

/-- パラメータ系の成分ごとの `q` 乗に対する通常の Euler 数は `q^h e((z), D)`。
二つの既存の重複度の入力を明示的に適用する。 -/
theorem chiOrd_koszul_pow {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z)
    (q : ℕ) (hq : 0 < q) :
    chiOrd (koszulComplex (fun j ↦ z j ^ q)) =
      (q : ℝ) ^ h * (multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
  have hp := multiplicity_eq_koszulEulerChar_of_residue_surjective D D
    (show Function.Injective (algebraMap D D) from Function.injective_id)
    (show Function.Surjective ((residue D).comp (algebraMap D D)) from residue_surjective)
    (fun j ↦ z j ^ q) (hz.pow D q hq)
  have he : algebraMap D D ∘ (fun j ↦ z j ^ q) = (fun j ↦ z j ^ q) := funext fun _ ↦ rfl
  rw [he, koszulEulerChar_self, multiplicity_parameter_pow D z hz q hq] at hp
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] using hp.symm

omit [IsLocalRing D] [IsNoetherianRing D] in
/-- 通常の Koszul Euler 数は `[-h, 0]` の有限和である。 -/
lemma chiOrd_koszul_eq_sum {h : ℕ} (z : Fin h → D) :
    chiOrd (koszulComplex z) =
      ∑ i ∈ Finset.Icc (-(h : ℤ)) 0,
        ((i.negOnePow : ℤ) : ℝ) *
          ((Module.length D ((koszulComplex z).homology i)).toNat : ℝ) := by
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hn
  have hi' : i < -(h : ℤ) ∨ 0 < i := by
    simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hn
  have hX : CategoryTheory.Limits.IsZero ((koszulComplex z).X i) := hi'.elim
    (koszulComplex_isZero_X_of_lt z i) (koszulComplex_isZero_X_of_pos z i)
  have := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X _ _ hX)
  exact hi (by simp [Module.length_eq_zero])

/-- 高次 Koszul ホモロジーの正規化長さが零へ収束すれば、パラメータ系の成分ごとの冪で
作った商の正規化長さは重複度へ収束する。冪の列は任意の正の整数列でよい。 -/
theorem normalized_parameter_quotient_tendsto_of_higher_koszul
    {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z)
    (q : ℕ → ℕ) (hq : ∀ n, 0 < q n)
    (hlim : ∀ i : ℤ, i < 0 → Tendsto (fun n ↦
      ((Module.length D ((koszulComplex (fun j ↦ z j ^ q n)).homology i)).toNat : ℝ) /
        (q n : ℝ) ^ h) atTop (nhds 0)) :
    Tendsto (fun n ↦
      ((Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ q n))).toNat : ℝ) /
        (q n : ℝ) ^ h) atTop
      (nhds (multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
  let s := Finset.Icc (-(h : ℤ)) 0
  let a (n : ℕ) (i : ℤ) :=
    ((Module.length D ((koszulComplex (fun j ↦ z j ^ q n)).homology i)).toNat : ℝ) /
      (q n : ℝ) ^ h
  let f (n : ℕ) (i : ℤ) := ((i.negOnePow : ℤ) : ℝ) * a n i
  have hzero : (0 : ℤ) ∈ s := by simp [s]
  have hsum (n : ℕ) : ∑ i ∈ s, f n i =
      (multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
    have he := congrArg (fun x : ℝ ↦ x / (q n : ℝ) ^ h)
      (chiOrd_koszul_pow D z hz (q n) (hq n))
    rw [chiOrd_koszul_eq_sum, Finset.sum_div] at he
    have hne : (q n : ℝ) ^ h ≠ 0 := pow_ne_zero _ (by exact_mod_cast (hq n).ne')
    simpa only [s, f, a, mul_div_assoc, mul_div_cancel_left₀ _ hne] using he
  have herror : Tendsto (fun n ↦ ∑ i ∈ s.erase 0, f n i) atTop (nhds 0) := by
    have hl : ∀ i ∈ s.erase 0, Tendsto (fun n ↦ f n i) atTop (nhds (0 : ℝ)) := by
      intro i hi
      have hi' : i < 0 := lt_of_le_of_ne
        (Finset.mem_Icc.mp (Finset.mem_erase.mp hi).2).2 (Finset.mem_erase.mp hi).1
      simpa only [mul_zero] using (hlim i hi').const_mul ((i.negOnePow : ℤ) : ℝ)
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (s.erase 0) hl
  have hterm (n : ℕ) : a n 0 =
      (multiplicity D (Ideal.span (Set.range z)) D : ℝ) - ∑ i ∈ s.erase 0, f n i := by
    have he := Finset.sum_erase_add s (f n) hzero
    rw [hsum] at he
    have hf : f n 0 = a n 0 := by simp [f]
    rw [hf] at he
    linarith
  have hmain : Tendsto (fun n ↦ a n 0) atTop
      (nhds (multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
    simpa only [hterm, sub_zero] using tendsto_const_nhds.sub herror
  have hquot (n : ℕ) : a n 0 =
      ((Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ q n))).toNat : ℝ) /
        (q n : ℝ) ^ h := by
    dsimp only [a]
    rw [(koszulComplex_homology_zero_equiv (fun j ↦ z j ^ q n)).some.length_eq]
  simpa only [hquot] using hmain

/-- 前の極限比較を、正規化長さと同じ値域 `ℝ≥0∞` で述べる。
有限長性・重複度の非負性を確認して実数値の極限と往復する。 -/
theorem normalized_parameter_quotient_tendsto_ennreal_of_higher_koszul
    {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z)
    (q : ℕ → ℕ) (hq : ∀ n, 0 < q n)
    (hlim : ∀ i : ℤ, i < 0 → Tendsto (fun n ↦
      (Module.length D ((koszulComplex (fun j ↦ z j ^ q n)).homology i) : ℝ≥0∞) /
        (q n : ℝ≥0∞) ^ h) atTop (nhds 0)) :
    Tendsto (fun n ↦
      (Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ q n)) : ℝ≥0∞) /
        (q n : ℝ≥0∞) ^ h) atTop
      (nhds (ENNReal.ofReal (multiplicity D (Ideal.span (Set.range z)) D : ℝ))) := by
  have hreal := normalized_parameter_quotient_tendsto_of_higher_koszul D z hz q hq
    (fun i hi ↦ by
      have he := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp (hlim i hi)
      simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
        toReal_toENNReal, ENNReal.toReal_zero] using he)
  have hfinite n : Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ q n)) ≠ ⊤ := by
    rw [← (koszulComplex_homology_zero_equiv (fun j ↦ z j ^ q n)).some.length_eq]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_koszulHomology_of_isSystemOfParameters D _ (hz.pow D _ (hq n)) 0)
  have hepos : 0 ≤ (multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
    exact_mod_cast (multiplicity_pos D _ hz.2).le
  apply (ENNReal.tendsto_toReal_iff (fun n ↦ ENNReal.div_ne_top
    (ENat.toENNReal_ne_top.mpr (hfinite n))
    (pow_ne_zero h (by exact_mod_cast (hq n).ne'))) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    toReal_toENNReal, ENNReal.toReal_ofReal hepos] using hreal

end SerrePositivity.HilbertSamuel
