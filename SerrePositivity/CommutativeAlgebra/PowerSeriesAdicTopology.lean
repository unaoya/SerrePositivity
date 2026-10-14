module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-! # 有限変数の冪級数環の変数イデアル進位相

離散係数の積位相を変数イデアル進位相と同定する。
変数イデアルの冪の係数判定は、Mathlib の多項式の完備化との同型を使う。
-/

@[expose] public section
namespace SerrePositivity

variable {σ R : Type*} [Finite σ] [CommRing R]

/-- 変数イデアルの n 乗への所属は、次数 n 未満の係数が消えることと同値。 -/
theorem mem_powerSeries_variables_pow_iff (n : ℕ) (f : MvPowerSeries σ R) :
    f ∈ (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) ^ n ↔
      ∀ d : σ →₀ ℕ, d.degree < n → MvPowerSeries.coeff d f = 0 := by
  let P := MvPolynomial.idealOfVars σ R
  let J := Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))
  let e := (MvPowerSeries.toAdicCompletionAlgEquiv σ R).toRingEquiv
  have he : J.map e = P.map
      (algebraMap (MvPolynomial σ R) (AdicCompletion P (MvPolynomial σ R))) := by
    simp_rw [J, P, MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp [e, P, MvPolynomial.idealOfVars, AdicCompletion.algebraMap_apply,
      ← MvPolynomial.coe_X, MvPowerSeries.toAdicCompletion_coe]
  have hm : f ∈ J ^ n ↔ e f ∈ (P ^ n).map
      (algebraMap (MvPolynomial σ R) (AdicCompletion P (MvPolynomial σ R))) := by
    rw [Ideal.map_pow, ← he, ← Ideal.map_pow]
    constructor
    · exact Ideal.mem_map_of_mem e
    · intro h
      obtain ⟨g, hg, hgf⟩ := (Ideal.mem_map_of_equiv e (e f)).mp h
      exact e.injective hgf ▸ hg
  rw [hm]
  change e f ∈ ((P ^ n).map (algebraMap (MvPolynomial σ R)
    (AdicCompletion P (MvPolynomial σ R)))).restrictScalars (MvPolynomial σ R) ↔ _
  rw [← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R)]
  change (MvPowerSeries.toAdicCompletion σ R f).val n = 0 ↔ _
  rw [MvPowerSeries.toAdicCompletion_apply_eq_mk_truncTotal, Ideal.Quotient.eq_zero_iff_mem]
  simp only [smul_eq_mul, Ideal.mul_top]
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h d hd
    simpa [MvPowerSeries.coeff_truncTotal_eq_ite, hd] using h d hd
  · intro h d hd
    simpa [MvPowerSeries.coeff_truncTotal_eq_ite, hd] using h d hd

open scoped MvPowerSeries.WithPiTopology
open Topology

variable [TopologicalSpace R] [DiscreteTopology R]

/-- 離散係数・有限変数の積位相は、変数イデアル進位相に等しい。 -/
theorem powerSeries_piTopology_isAdic_variables :
    IsAdic (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) := by
  classical
  rw [isAdic_iff]
  constructor
  · intro n
    let T := (Finsupp.finite_of_degree_lt (σ := σ) n).toFinset
    have he : (((Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) ^ n :
        Ideal (MvPowerSeries σ R)) : Set (MvPowerSeries σ R)) =
          ⋂ d ∈ T, {f | MvPowerSeries.coeff d f = 0} := by
      ext f
      simp [mem_powerSeries_variables_pow_iff, T]
    rw [he]
    exact isOpen_biInter_finset (fun d _ ↦
      (isOpen_discrete ({0} : Set R)).preimage (MvPowerSeries.WithPiTopology.continuous_coeff R d))
  · intro s hs
    let s' : Set ((σ →₀ ℕ) → R) := s
    have hs' : s' ∈ 𝓝 (fun _ ↦ (0 : R)) := hs
    rw [nhds_pi] at hs'
    obtain ⟨T, t, ht, hsub⟩ := Filter.mem_pi'.mp hs'
    refine ⟨T.sup Finsupp.degree + 1, ?_⟩
    intro f hf
    apply hsub
    intro d hd
    have hdeg : d.degree < T.sup Finsupp.degree + 1 :=
      (Finset.le_sup (show d ∈ T from hd)).trans_lt (Nat.lt_succ_self _)
    have hz := (mem_powerSeries_variables_pow_iff _ f).mp hf d hdeg
    change MvPowerSeries.coeff d f ∈ t d
    rw [hz]
    exact mem_of_mem_nhds (ht d)

/-- 積位相での連続性と変数イデアル進位相での連続性を移す入口。 -/
theorem powerSeries_continuous_iff_variables_adic {M : Type*} [TopologicalSpace M]
    (f : MvPowerSeries σ R → M) :
    Continuous f ↔ @Continuous (MvPowerSeries σ R) M
      (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).adicTopology
        inferInstance f := by
  have ht : (inferInstance : TopologicalSpace (MvPowerSeries σ R)) =
      (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).adicTopology :=
    powerSeries_piTopology_isAdic_variables
  exact Iff.of_eq (congrArg (fun t ↦ @Continuous (MvPowerSeries σ R) M t inferInstance f) ht)

end SerrePositivity
