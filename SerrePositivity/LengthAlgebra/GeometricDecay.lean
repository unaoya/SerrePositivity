module

public import SerrePositivity.PerfectComplex.NormalizedLength
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # 幾何的に減少する上界から正規化長さ零を導く

有限段の長さ計算を拡張非負実数値のまま扱い、無限大を実数の零へ落とさずに
幾何的な上界から零を導く。環や加群の追加の有限性は不要。
-/

@[expose] public section
universe u
namespace SerrePositivity
open Filter Topology
open scoped ENNReal

/-- 有限な定数と比率1未満の冪による上界があれば、拡張非負実数値は零。 -/
theorem ennreal_eq_zero_of_geometric_bound (a c r : ℝ≥0∞) (hc : c ≠ ⊤) (hr : r < 1)
    (hbound : ∀ n : ℕ, a ≤ c * r ^ n) : a = 0 := by
  have hlim : Tendsto (fun n : ℕ ↦ c * r ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr hc)
  exact le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) bot_le

/-- 指数的に増大する分母で割った一様な有限上界から零を導く。 -/
theorem ennreal_eq_zero_of_div_pow_bound (a c r : ℝ≥0∞) (hc : c ≠ ⊤) (hr : 1 < r)
    (hbound : ∀ n : ℕ, a ≤ c / r ^ n) : a = 0 := by
  apply ennreal_eq_zero_of_geometric_bound a c r⁻¹ hc
    (ENNReal.inv_lt_one.mpr hr)
  simpa only [div_eq_mul_inv, ENNReal.inv_pow] using hbound

namespace NormalizedLength
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 巡回商のイデアルを拡大すると、冪ねじれな源の長さ以下になる。 -/
theorem len_quotient_le_of_pow_le (n : ℕ) (I K : Ideal R) (hJI : J ^ n ≤ I)
    (hIK : I ≤ K) : lam.len (R ⧸ K) ≤ lam.len (R ⧸ I) := by
  have htor : IsPowTorsion J (R ⧸ I) := by
    refine ⟨n, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
    exact hJI
  exact lam.len_le_of_surjective (Ideal.Quotient.factorₐ R hIK).toLinearMap
    (Ideal.Quotient.factor_surjective hIK) htor

/-- 冪ねじれな巡回商を幾何的に小さい巡回商から覆えば、目的の長さは零。 -/
theorem len_quotient_eq_zero_of_geometric_covers
    (n : ℕ) (K : Ideal R) (I : ℕ → Ideal R)
    (hJI : ∀ m, J ^ n ≤ I m) (hIK : ∀ m, I m ≤ K)
    (c r : ℝ≥0∞) (hc : c ≠ ⊤) (hr : r < 1)
    (hbound : ∀ m, lam.len (R ⧸ I m) ≤ c * r ^ m) : lam.len (R ⧸ K) = 0 :=
  ennreal_eq_zero_of_geometric_bound _ c r hc hr fun m ↦
    (lam.len_quotient_le_of_pow_le n (I m) K (hJI m) (hIK m)).trans (hbound m)

/-- 一様な冪ねじれ条件と指数的な分母による巡回商の上界から長さ零を得る。 -/
theorem len_quotient_eq_zero_of_div_pow_covers
    (n : ℕ) (K : Ideal R) (I : ℕ → Ideal R)
    (hJI : ∀ m, J ^ n ≤ I m) (hIK : ∀ m, I m ≤ K)
    (c r : ℝ≥0∞) (hc : c ≠ ⊤) (hr : 1 < r)
    (hbound : ∀ m, lam.len (R ⧸ I m) ≤ c / r ^ m) : lam.len (R ⧸ K) = 0 :=
  ennreal_eq_zero_of_div_pow_bound _ c r hc hr fun m ↦
    (lam.len_quotient_le_of_pow_le n (I m) K (hJI m) (hIK m)).trans (hbound m)

end NormalizedLength
end SerrePositivity
