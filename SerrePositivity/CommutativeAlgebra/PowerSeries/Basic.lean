module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # 有限変数の冪級数環の基本構造

概要：有限変数の冪級数環 `R[[X]]` について
- 標数は `R` と同じ。`R` が整域なら整域。
- `f ∈ (X)^n` は全次数 `n` 未満の係数が零であることと同値。離散係数の積位相は `(X)` 進位相。
- 定数項の核は `(X)`。`R` が局所なら極大イデアルは `m_R R[[X]] + (X)`。
- 係数の全射は冪級数の全射を与え、核が有限生成なら核は係数の核の拡大。
方針：`(X)^n` の判定は Mathlib の多項式の完備化との同型 `MvPowerSeries.toAdicCompletionAlgEquiv` から読む。
規約：変数の有限性は `(X)^n` の判定とそこから従う主張にだけ使う。
使われ方：冪級数環の完備性・次元・評価（`PowerSeries/*`）、Cohen–Gabber と Witt の正規化、交点数の対角線論法。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Characteristic

/-- 定数の埋め込みは単射なので、冪級数環の標数は係数環と同じ。 -/
instance charP_mvPowerSeries (σ R : Type*) [CommSemiring R] (p : ℕ) [CharP R p] :
    CharP (MvPowerSeries σ R) p :=
  charP_of_injective_algebraMap MvPowerSeries.C_injective p

/-- 整域係数の多変数冪級数環は整域。Mathlibの零因子なしのインスタンスを使う。 -/
instance isDomain_mvPowerSeries (σ R : Type*) [CommRing R] [IsDomain R] :
    IsDomain (MvPowerSeries σ R) := NoZeroDivisors.to_isDomain _

end Characteristic

section AdicTopology

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

end AdicTopology

section LocalStructure

open IsLocalRing


/-- 有限変数冪級数の定数係数写像の核は、全変数が生成するイデアル。 -/
theorem powerSeries_ker_constantCoeff (σ R : Type*) [Finite σ] [CommRing R] :
    RingHom.ker (MvPowerSeries.constantCoeff (σ := σ) (R := R)) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))) := by
  ext f
  simpa [RingHom.mem_ker, Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] using
    (mem_powerSeries_variables_pow_iff 1 f).symm

/-- 局所係数環の有限変数冪級数の極大イデアルは、係数極大イデアルと全変数の和。 -/
theorem powerSeries_maximalIdeal_eq (σ R : Type*) [Finite σ] [CommRing R] [IsLocalRing R] :
    maximalIdeal (MvPowerSeries σ R) =
      (maximalIdeal R).map MvPowerSeries.C ⊔
        Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))) := by
  let f := MvPowerSeries.constantCoeff (σ := σ) (R := R)
  let : IsLocalHom f := ⟨fun _ h ↦ MvPowerSeries.isUnit_iff_constantCoeff.mpr h⟩
  rw [← maximalIdeal_comap f, ← powerSeries_ker_constantCoeff σ R]
  have hmap : ((maximalIdeal R).map (MvPowerSeries.C (σ := σ))).map f =
      maximalIdeal R := by
    rw [Ideal.map_map]
    have he : f.comp MvPowerSeries.C = RingHom.id R := by ext; simp [f]
    rw [he, Ideal.map_id]
  nth_rw 1 [← hmap]
  rw [Ideal.comap_map_of_surjective f (fun r ↦ ⟨MvPowerSeries.C r, by simp [f]⟩)]
  rfl


/-- 形式変数は局所係数環の冪級数環の極大イデアルに入る。 -/
theorem powerSeries_variables_le_maximalIdeal
    (σ R : Type*) [CommRing R] [IsLocalRing R] :
    Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))) ≤
      IsLocalRing.maximalIdeal (MvPowerSeries σ R) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change MvPowerSeries.X i ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ R)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  simp

end LocalStructure

section CoefficientQuotient

universe u v

/-- 係数全射は、冪級数環の係数ごとの写像でも全射となる。 -/
theorem powerSeries_map_surjective {R S : Type u} [CommRing R] [CommRing S]
    (σ : Type v) (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (MvPowerSeries.map (σ := σ) f) := by
  intro φ
  choose a ha using fun d : σ →₀ ℕ ↦ hf (MvPowerSeries.coeff d φ)
  refine ⟨a, ?_⟩
  ext d
  exact ha d

/-- 係数写像の核が有限生成なら、係数の核の拡大で割った冪級数環は終域の冪級数環。 -/
def powerSeriesCoefficientQuotientEquiv {R S : Type u} [CommRing R] [CommRing S]
    (σ : Type v) (f : R →+* S) (hf : Function.Surjective f) (hker : (RingHom.ker f).FG) :
    MvPowerSeries σ R ⧸ (RingHom.ker f).map MvPowerSeries.C ≃+* MvPowerSeries σ S :=
  (Ideal.quotEquivOfEq (MvPowerSeries.ker_map_of_fg f hker).symm).trans
    (RingHom.quotientKerEquivOfSurjective (powerSeries_map_surjective σ f hf))

@[simp] theorem powerSeriesCoefficientQuotientEquiv_mk
    {R S : Type u} [CommRing R] [CommRing S] (σ : Type v) (f : R →+* S)
    (hf : Function.Surjective f) (hker : (RingHom.ker f).FG) (φ : MvPowerSeries σ R) :
    powerSeriesCoefficientQuotientEquiv σ f hf hker (Ideal.Quotient.mk _ φ) =
      MvPowerSeries.map f φ := rfl

end CoefficientQuotient

section Injective

/-- 単射な冪級数評価の変数の像は非零。 -/
theorem powerSeries_variable_image_ne_zero
    {k D σ : Type*} [CommRing k] [Nontrivial k] [CommRing D]
    (F : MvPowerSeries σ k →+* D) (hF : Function.Injective F) (i : σ) :
    F (MvPowerSeries.X i) ≠ 0 := by
  intro hz
  have hX : (MvPowerSeries.X i : MvPowerSeries σ k) = 0 := hF (hz.trans F.map_zero.symm)
  have h := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) hX
  exact one_ne_zero (by
    simpa only [MvPowerSeries.coeff_index_single_self_X, map_zero] using h)

end Injective

end SerrePositivity
