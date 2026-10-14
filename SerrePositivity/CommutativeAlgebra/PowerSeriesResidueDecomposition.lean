module

public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Fin

/-! # 有限変数冪級数の指数剰余による分解

各指数を q で割った剰余ごとに係数を集める。完全標数 p の完全係数環では、
これに係数の逆 Frobenius を適用して、冪級数を単項式と p^n 乗の有限和にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- 有限個の剰余から指数を作る。 -/
def powerSeriesResidueExponent (q : ℕ) (e : σ → Fin q) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦ (e i : ℕ))

@[simp] theorem powerSeriesResidueExponent_apply (q : ℕ) (e : σ → Fin q) (i : σ) :
    powerSeriesResidueExponent q e i = (e i : ℕ) := rfl

/-- 指数の各成分の剰余。 -/
def powerSeriesResidueIndex (q : ℕ) (hq : 0 < q) (d : σ →₀ ℕ) : σ → Fin q :=
  fun i ↦ ⟨d i % q, Nat.mod_lt _ hq⟩

/-- 指数の各成分の商。 -/
def powerSeriesQuotientExponent (q : ℕ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (fun a ↦ a / q) (Nat.zero_div q)

/-- 一つの剰余類に属する係数を集めた冪級数。 -/
def powerSeriesResidueComponent (q : ℕ) (e : σ → Fin q)
    (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d ↦ MvPowerSeries.coeff (q • d + powerSeriesResidueExponent q e) φ

theorem powerSeries_exponent_division (q : ℕ) (hq : 0 < q) (d : σ →₀ ℕ) :
    q • powerSeriesQuotientExponent q d +
      powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d) = d := by
  ext i
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    powerSeriesQuotientExponent, Finsupp.mapRange_apply,
    powerSeriesResidueExponent_apply, powerSeriesResidueIndex]
  exact Nat.div_add_mod (d i) q

theorem coeff_powerSeriesResidueTerm (q : ℕ) (hq : 0 < q) (e : σ → Fin q)
    (φ : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d
      (MvPowerSeries.monomial (powerSeriesResidueExponent q e) 1 *
        MvPowerSeries.expand q (Nat.ne_of_gt hq) (powerSeriesResidueComponent q e φ)) =
      if e = powerSeriesResidueIndex q hq d then MvPowerSeries.coeff d φ else 0 := by
  classical
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases he : e = powerSeriesResidueIndex q hq d
  · subst e
    have hdiv := powerSeries_exponent_division q hq d
    have hle : powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d) ≤ d := by
      calc
        _ ≤ q • powerSeriesQuotientExponent q d +
            powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d) :=
          le_add_of_nonneg_left zero_le
        _ = d := hdiv
    have hsub : d - powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d) =
        q • powerSeriesQuotientExponent q d := by
      calc
        _ = (q • powerSeriesQuotientExponent q d +
            powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d)) -
            powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d) :=
          congrArg (fun x ↦ x - powerSeriesResidueExponent q
            (powerSeriesResidueIndex q hq d)) hdiv.symm
        _ = _ := add_tsub_cancel_right _ _
    rw [ite_eq_left hle, hsub, MvPowerSeries.coeff_expand_smul, ite_eq_left rfl, one_mul]
    change MvPowerSeries.coeff
      (q • powerSeriesQuotientExponent q d +
        powerSeriesResidueExponent q (powerSeriesResidueIndex q hq d)) φ = _
    rw [hdiv]
  · rw [ite_eq_right he]
    split_ifs with hle
    · obtain ⟨i, hi⟩ : ∃ i, e i ≠ powerSeriesResidueIndex q hq d i := by
        by_contra! h
        exact he (funext h)
      have hnot : ¬ q ∣ (d - powerSeriesResidueExponent q e) i := by
        intro hdvd
        have hli : (e i : ℕ) ≤ d i := hle i
        have hm := Nat.mod_eq_zero_of_dvd hdvd
        have hi' : (e i : ℕ) ≠ d i % q := by
          intro h
          apply hi
          exact Fin.ext h
        simp only [Finsupp.tsub_apply, powerSeriesResidueExponent_apply] at hm
        have hemod := Nat.mod_eq_of_lt (e i).isLt
        have hsum := Nat.add_mod (d i - (e i : ℕ)) (e i : ℕ) q
        rw [Nat.sub_add_cancel hli, hm, hemod, zero_add, hemod] at hsum
        exact hi' hsum.symm
      rw [MvPowerSeries.coeff_expand_of_not_dvd q (Nat.ne_of_gt hq) _ hnot, mul_zero]
    · rfl

open Classical in
/-- 冪級数の指数剰余分解。係数環の完全性はまだ必要ない。 -/
theorem powerSeries_residue_decomposition (q : ℕ) (hq : 0 < q)
    (φ : MvPowerSeries σ R) :
    φ = ∑ e : σ → Fin q,
      MvPowerSeries.monomial (powerSeriesResidueExponent q e) 1 *
        MvPowerSeries.expand q (Nat.ne_of_gt hq) (powerSeriesResidueComponent q e φ) := by
  classical
  ext d
  simp only [map_sum, coeff_powerSeriesResidueTerm q hq]
  simp

omit [Fintype σ] in
/-- 完全係数環上では、変数の指数の展開は係数の逆 Frobenius の p^n 乗になる。 -/
theorem powerSeries_expand_eq_frobeniusRoot_pow (p : ℕ) [Fact p.Prime]
    [CharP R p] [PerfectRing R p] (n : ℕ) (φ : MvPowerSeries σ R) :
    MvPowerSeries.expand (p ^ n) (pow_ne_zero n (Fact.out : p.Prime).ne_zero) φ =
      (MvPowerSeries.map (iterateFrobeniusEquiv R p n).symm.toRingHom φ) ^ (p ^ n) := by
  rw [← MvPowerSeries.map_iterateFrobenius_expand p (Fact.out : p.Prime).ne_zero,
    MvPowerSeries.map_expand]
  congr 1
  ext d
  simp only [MvPowerSeries.coeff_map]
  exact ((iterateFrobeniusEquiv R p n).apply_symm_apply _).symm

open Classical in
/-- 任意の有限変数冪級数は、剰余単項式と p^n 乗の有限和として表せる。 -/
theorem powerSeries_exists_monomial_frobenius_decomposition (p : ℕ) [Fact p.Prime]
    [CharP R p] [PerfectRing R p] (n : ℕ) (φ : MvPowerSeries σ R) :
    ∃ ψ : (σ → Fin (p ^ n)) → MvPowerSeries σ R,
      φ = ∑ e : σ → Fin (p ^ n),
        MvPowerSeries.monomial (powerSeriesResidueExponent (p ^ n) e) 1 * ψ e ^ (p ^ n) := by
  refine ⟨fun e ↦ MvPowerSeries.map (iterateFrobeniusEquiv R p n).symm.toRingHom
    (powerSeriesResidueComponent (p ^ n) e φ), ?_⟩
  calc
    φ = ∑ e : σ → Fin (p ^ n),
        MvPowerSeries.monomial (powerSeriesResidueExponent (p ^ n) e) 1 *
          MvPowerSeries.expand (p ^ n) (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
            (powerSeriesResidueComponent (p ^ n) e φ) :=
      powerSeries_residue_decomposition (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) φ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [powerSeries_expand_eq_frobeniusRoot_pow]

omit [Fintype σ] in
/-- p^n 乗とすべての変数を像に含む射は、完全係数の有限変数冪級数環へ全射。 -/
theorem powerSeries_surjective_of_powers_and_variables {S : Type*} [CommRing S]
    [Finite σ]
    (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p] (n : ℕ)
    (f : S →+* MvPowerSeries σ R)
    (hpow : ∀ φ : MvPowerSeries σ R, φ ^ (p ^ n) ∈ f.range)
    (hX : ∀ i : σ, MvPowerSeries.X i ∈ f.range) : Function.Surjective f := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  intro φ
  obtain ⟨ψ, hψ⟩ := powerSeries_exists_monomial_frobenius_decomposition p n φ
  change φ ∈ f.range
  rw [hψ]
  apply Subring.sum_mem
  intro e _
  apply Subring.mul_mem
  · rw [MvPowerSeries.monomial_one_eq, Finsupp.prod]
    apply Subring.prod_mem
    intro i _
    exact Subring.pow_mem _ (hX i) _
  · exact hpow (ψ e)

end SerrePositivity
