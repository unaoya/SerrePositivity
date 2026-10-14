module

public import SerrePositivity.CommutativeAlgebra.QuotientPowerLength
public import SerrePositivity.CommutativeAlgebra.PrescribedParameter
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # 非零因子による商のFrobenius長さの低次元上界

次元r+1のNoether局所環の非零因子gにr個のパラメータを補い、
生成元の冪による長さ評価からO(p^(nr))を得る。
Hilbert–Kunz重複度の存在やHilbert–Samuel多項式を入力にしない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open IsLocalRing
open Filter Topology
open scoped ENNReal

/-- 極大イデアルを根基にもつ関係式による商は有限長。 -/
theorem isFiniteLength_quotient_of_radical_eq_maximalIdeal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = maximalIdeal R) : IsFiniteLength R (R ⧸ I) := by
  let : IsArtinianRing (R ⧸ maximalIdeal R) :=
    inferInstanceAs (IsArtinianRing (ResidueField R))
  apply isFiniteLength_of_le_radical_annihilator (maximalIdeal R)
  rw [Ideal.annihilator_quotient, hI]

/-- 非零因子gで割ったFrobenius商の長さは、次元より一つ小さい指数で一様に抑えられる。
定数は実際に選んだパラメータ商の有限長さを自然数として取る。 -/
theorem exists_frobenius_hypersurface_length_bound
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : ℕ) [ExpChar R p] (g : R) (hg : g ∈ nonZeroDivisors R)
    (hgm : g ∈ maximalIdeal R) {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ∃ c : ℕ, ∀ n : ℕ,
      Module.length R (R ⧸ ((maximalIdeal R).map (iterateFrobenius R p n) ⊔ Ideal.span {g})) ≤
        ((p ^ n : ℕ) : ℕ∞) ^ r * (c : ℕ∞) := by
  obtain ⟨z, hz, hrad⟩ := exists_parameters_completing_nonZeroDivisor R g hg hgm hdim
  let I := Ideal.span {g} ⊔ Ideal.span (Set.range z)
  have hfinite : IsFiniteLength R (R ⧸ I) :=
    isFiniteLength_quotient_of_radical_eq_maximalIdeal R I hrad
  have hlen : Module.length R (R ⧸ I) ≠ ⊤ := Module.length_ne_top_iff.mpr hfinite
  refine ⟨(Module.length R (R ⧸ I)).toNat, fun n ↦ ?_⟩
  rw [ENat.natCast_toNat hlen]
  exact length_quotient_frobenius_sup_le R (Ideal.span {g}) (maximalIdeal R) z hz p n

/-- 次元r+1の分母で正規化すると、非零因子の商の上界はc/p^nとなる。
無限大を実数化せず、拡張非負実数で割り算を行う。 -/
theorem exists_frobenius_hypersurface_normalized_bound
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : ℕ) [ExpChar R p] (g : R) (hg : g ∈ nonZeroDivisors R)
    (hgm : g ∈ maximalIdeal R) {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ∃ c : ℕ, ∀ n : ℕ,
      (Module.length R (R ⧸ ((maximalIdeal R).map (iterateFrobenius R p n) ⊔
        Ideal.span {g})) : ℝ≥0∞) / ((p : ℝ≥0∞) ^ n) ^ (r + 1) ≤
          (c : ℝ≥0∞) / (p : ℝ≥0∞) ^ n := by
  obtain ⟨c, hc⟩ := exists_frobenius_hypersurface_length_bound R p g hg hgm hdim
  refine ⟨c, fun n ↦ ?_⟩
  have hn : (Module.length R (R ⧸ ((maximalIdeal R).map (iterateFrobenius R p n) ⊔
      Ideal.span {g})) : ℝ≥0∞) ≤ ((p : ℝ≥0∞) ^ n) ^ r * (c : ℝ≥0∞) := by
    exact_mod_cast hc n
  refine (ENNReal.div_le_div_right hn _).trans_eq ?_
  rw [pow_succ]
  exact ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ (by
    exact_mod_cast (expChar_pos R p).ne'))) (by simp)

/-- 正規化したFrobenius商の長さは零に収束する。重複度の存在定理は使わない。 -/
theorem tendsto_frobenius_hypersurface_normalized_length_zero
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : ℕ) [ExpChar R p] (hp : 1 < p) (g : R) (hg : g ∈ nonZeroDivisors R)
    (hgm : g ∈ maximalIdeal R) {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    Tendsto (fun n : ℕ ↦
      (Module.length R (R ⧸ ((maximalIdeal R).map (iterateFrobenius R p n) ⊔
        Ideal.span {g})) : ℝ≥0∞) / ((p : ℝ≥0∞) ^ n) ^ (r + 1)) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_frobenius_hypersurface_normalized_bound R p g hg hgm hdim
  have hlim : Tendsto (fun n : ℕ ↦ (c : ℝ≥0∞) / (p : ℝ≥0∞) ^ n) atTop (𝓝 0) := by
    simp only [div_eq_mul_inv, ENNReal.inv_pow]
    have hr : (p : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.mpr (by exact_mod_cast hp)
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr (by simp : (c : ℝ≥0∞) ≠ ⊤))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) hc

/-- 固定した非零因子のk乗を関係式に使う場合も、同じ定数で倍率kを保持して評価できる。
根の指数と有限段の差から生じるg^(p^(m-n))に適用する。 -/
theorem exists_frobenius_hypersurface_power_length_bound
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : ℕ) [ExpChar R p] (g : R) (hg : g ∈ nonZeroDivisors R)
    (hgm : g ∈ maximalIdeal R) {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ∃ c : ℕ, ∀ m k : ℕ,
      Module.length R (R ⧸ ((maximalIdeal R).map (iterateFrobenius R p m) ⊔
        Ideal.span {g ^ k})) ≤
          (k : ℕ∞) * (((p ^ m : ℕ) : ℕ∞) ^ r * (c : ℕ∞)) := by
  obtain ⟨c, hc⟩ := exists_frobenius_hypersurface_length_bound R p g hg hgm hdim
  refine ⟨c, fun m k ↦ ?_⟩
  exact (length_quotient_sup_span_pow_le R
    ((maximalIdeal R).map (iterateFrobenius R p m)) g k).trans (mul_le_mul_right (hc m) _)

end SerrePositivity
