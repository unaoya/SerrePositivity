module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.AssociatedGraded
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Dimension
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.ReesPresentation
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Polynomial
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Graded.PolynomialRing

/-! # 随伴次数環の多項式表示と生成元の正則性

## 概要

Noether 局所環 `R` の極大イデアルを次元と同数の元 `z` で生成すると、随伴次数環 `gr_m(R)` の
`R/m` 上の多項式環による表示は単射（`gradedReesPresentation_injective_of_span_eq_maximalIdeal`）で、
各生成元 `z_i` は `R` の正則元（`isSMulRegular_generator_of_span_eq_maximalIdeal`）。

## 方針

- 表示が単射なら、多項式の変数は随伴次数環の各次数で単射に作用し
  （`gradedMultiplication_injective_of_gradedReesPresentation_injective`）、
  Krull の共通部分定理でその正則性が `R` へ持ち上がる（`isSMulRegular_of_gradedMultiplication_injective`）。
- 単射性：非零の斉次関係があると累積 Hilbert 関数の増大度が生成元の個数より小さくなり、
  個数が次元に等しいことと Samuel の次元定理に反する。

## 規約

正則列・整域性・非混合性の入力は使わない。名前空間は `HilbertSamuel`。

## 使われ方

正則系は正則列であること（`RegularLocalRing/Basic`）と CLMST の巡回 perfectoid 化。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSamuel

section Lift

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- Degreewise regularity gives the exact inverse-image identity for the
filtration. No separatedness or finiteness assumptions are needed here. -/
theorem comap_pow_smul_top_eq_of_gradedMultiplication_injective
    (I : Ideal R) (x : I)
    (hx : ∀ n, Function.Injective (gradedMultiplication R I M x n)) (n : ℕ) :
    (I ^ (n + 1) • ⊤ : Submodule R M).comap (LinearMap.lsmul R M (x : R)) =
      I ^ n • ⊤ := by
  apply le_antisymm
  · intro m hm
    change (x : R) • m ∈ I ^ (n + 1) • (⊤ : Submodule R M) at hm
    induction n with
    | zero => simp
    | succ n ih =>
      have hmn : m ∈ adicSubmodule R I M n := ih
        (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) le_rfl hm)
      let a : adicSubmodule R I M n := ⟨m, hmn⟩
      have hzero : gradedMultiplication R I M x n (Submodule.Quotient.mk a) = 0 := by
        rw [gradedMultiplication_mk, Submodule.Quotient.mk_eq_zero]
        exact hm
      have ha : (Submodule.Quotient.mk a : GradedPiece R I M n) = 0 :=
        hx n (hzero.trans (map_zero _).symm)
      rw [Submodule.Quotient.mk_eq_zero] at ha
      exact ha
  · intro m hm
    exact smul_mem_adicSubmodule R I M x hm

/-- Krull intersection lifts regularity of the initial form to regularity on
the module itself. The ideal may be any proper ideal of the local ring. -/
theorem isSMulRegular_of_gradedMultiplication_injective [IsNoetherianRing R]
    [IsLocalRing R] [Module.Finite R M] (I : Ideal R) (hI : I ≠ ⊤) (x : I)
    (hx : ∀ n, Function.Injective (gradedMultiplication R I M x n)) :
    IsSMulRegular M (x : R) := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro m hm
  have hall : m ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) := by
    rw [Submodule.mem_iInf]
    intro n
    rw [← comap_pow_smul_top_eq_of_gradedMultiplication_injective I x hx n]
    change (x : R) • m ∈ I ^ (n + 1) • (⊤ : Submodule R M)
    rw [hm]
    exact Submodule.zero_mem _
  rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hI] at hall
  exact hall

end Lift

section FromPresentation

variable (R : Type u) [CommRing R] (I : Ideal R)
variable {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I)
variable (hinj : Function.Injective (gradedReesPresentation R I z hz))

include hz hinj

/-- The image of a polynomial variable is regular when the associated graded
presentation is an isomorphism. -/
theorem isSMulRegular_gradedReesPresentation_X (i : Fin s) :
    IsSMulRegular (GradedReesRing R I)
      (gradedReesPresentation R I z hz (MvPolynomial.X i)) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := gradedReesPresentation_surjective R I z hz a
  obtain ⟨b, rfl⟩ := gradedReesPresentation_surjective R I z hz b
  apply congrArg (gradedReesPresentation R I z hz)
  apply (MvPolynomial.isRegular_X (n := i)).left
  apply hinj
  simpa only [map_mul, smul_eq_mul] using hab

/-- Regularity of the variables transfers to injectivity in each associated
graded component. -/
theorem gradedMultiplication_injective_of_gradedReesPresentation_injective
    (i : Fin s) (n : ℕ) :
    Function.Injective (gradedMultiplication R I R
      ⟨z i, hz ▸ Ideal.subset_span (Set.mem_range_self i)⟩ n) := by
  let : Module (GradedReesRing R I) (ReesGraded R I R) := reesGraded_module R I R
  let : SMul (GradedReesRing R I) (ReesGraded R I R) :=
    (reesGraded_module R I R).toSMul
  let := gradedPolynomialModule R I R z hz
  let a := gradedReesPresentation R I z hz (MvPolynomial.X i)
  have ha : IsSMulRegular (ReesGraded R I R) a :=
    ((reesGradedSelfEquivOverGradedRing R I).isSMulRegular_congr a).mpr
      (isSMulRegular_gradedReesPresentation_X R I z hz hinj i)
  intro x y hxy
  apply gradedSingle_injective R I R n
  apply ha
  change (MvPolynomial.X i : MvPolynomial (Fin s) (R ⧸ I)) • gradedSingle R I R n x =
    (MvPolynomial.X i : MvPolynomial (Fin s) (R ⧸ I)) • gradedSingle R I R n y
  rw [gradedPolynomial_X_smul_single, gradedPolynomial_X_smul_single, hxy]

/-- Every ideal generator is regular on the original ring if its associated
graded presentation is injective. -/
theorem isSMulRegular_generator_of_gradedReesPresentation_injective
    [IsNoetherianRing R] [IsLocalRing R] (hI : I ≠ ⊤) (i : Fin s) :
    IsSMulRegular R (z i) :=
  isSMulRegular_of_gradedMultiplication_injective I hI
    ⟨z i, hz ▸ Ideal.subset_span (Set.mem_range_self i)⟩
    (gradedMultiplication_injective_of_gradedReesPresentation_injective R I z hz hinj i)

end FromPresentation

section Presentation

open IsLocalRing Polynomial Filter HilbertSerre

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The associated graded presentation is injective for a maximal-ideal family
whose positive length equals the ring dimension. -/
theorem gradedReesPresentation_injective_of_span_eq_maximalIdeal
    {s : ℕ} (z : Fin (s + 1) → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (he : ringKrullDim R = s + 1) :
    Function.Injective (gradedReesPresentation R (maximalIdeal R) z hz) := by
  classical
  let I := maximalIdeal R
  let k := R ⧸ I
  let : I.IsMaximal := maximalIdeal.isMaximal R
  let : Field k := Ideal.Quotient.field I
  let NS : ℕ → Submodule R (MvPolynomial (Fin (s + 1)) k) :=
    fun n => (MvPolynomial.homogeneousSubmodule (Fin (s + 1)) k n).restrictScalars R
  let NT := reesGrade R I R
  let : DirectSum.Decomposition NS := homogeneousDecompositionRestrictScalars R k (Fin (s + 1))
  let : DirectSum.Decomposition NT := (isInternal_reesGrade R I R).chooseDecomposition
  let F := gradedPresentationMap R I z hz
  have hdegree : ∀ n, ∀ x ∈ NS n, F x ∈ NT n :=
    gradedPresentationMap_mem_reesGrade R I z hz
  have hker := ker_isHomogeneous_of_degree NS NT F (d := 0) hdegree
  have hfinite : ∀ n, IsFiniteLength R (NS n) := by
    intro n
    apply Module.length_ne_top_iff.mp
    rw [homogeneousSubmodule_length_restrictScalars]
    exact Module.length_ne_top_iff.mpr
      (HilbertSerre.finiteLength_homogeneousSubmodule k (Fin (s + 1)) n)
  have hseries : lengthSeries NS = (PowerSeries.invOneSubPow ℚ (s + 1)).val := by
    rw [← HilbertSerre.lengthSeries_homogeneousSubmodule k (s + 1)]
    ext n
    simp only [lengthSeries, PowerSeries.coeff_mk]
    rw [homogeneousSubmodule_length_restrictScalars]
  have hI : I.radical = maximalIdeal R := (maximalIdeal.isMaximal R).isPrime.radical
  have hP := isSamuelPoly_poly_of_radical R I hI R
  have hcumulative : ∀ᶠ n : ℕ in atTop,
      cumulativeLength NT n = (poly R I R).eval (n : ℚ) := by
    filter_upwards [hP] with n hn
    rw [cumulativeLength_reesGrade R I R hI, hn.2]
  have hFinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot]
    apply (Submodule.eq_bot_iff _).mpr
    intro p hp
    by_contra hp0
    have hnonzero : ∃ n, gradeProjection NS n p ≠ 0 := by
      by_contra! hzero
      have hsum := DirectSum.sum_support_decompose NS p
      have hsumzero : (∑ n ∈ (DirectSum.decompose NS p).support,
          (DirectSum.decompose NS p n : MvPolynomial (Fin (s + 1)) k)) = 0 := by
        apply Finset.sum_eq_zero
        intro n _
        exact hzero n
      exact hp0 (hsum.symm.trans hsumzero)
    obtain ⟨d, hd⟩ := hnonzero
    let f := gradeProjection NS d p
    have hfhom : f.IsHomogeneous d := (DirectSum.decompose NS p d).2
    have hfker : F f = 0 := hker d hp
    have hrelation : ∀ g, F (f * g) = 0 := by
      have hfg : gradedReesPresentation R I z hz f = 0 := by
        apply (reesGradedSelfEquiv R I).symm.injective
        exact hfker.trans (reesGradedSelfEquiv R I).symm.map_zero.symm
      intro g
      change (reesGradedSelfEquiv R I).symm (gradedReesPresentation R I z hz (f * g)) = 0
      have hg : gradedReesPresentation R I z hz (f * g) = 0 := by
        rw [map_mul, hfg, zero_mul]
      exact (congrArg (reesGradedSelfEquiv R I).symm hg).trans
        (reesGradedSelfEquiv R I).symm.map_zero
    have hbound := HilbertSerre.natDegree_le_of_relation NS NT F
      (gradedPresentationMap_surjective R I z hz) hdegree f hd d
      (fun n x hx => by
        change x.IsHomogeneous n at hx
        change (f * x).IsHomogeneous (n + d)
        simpa only [Nat.add_comm] using hfhom.mul hx)
      hrelation hfinite s hseries (poly R I R) (hP.leadingCoeff_pos R hI) hcumulative
    have hdim : (poly R I R).natDegree = s + 1 := by
      rw [natDegree_poly_eq_dim R I hI]
      exact_mod_cast (natCast_dimToNat_ringKrullDim R).trans he
    omega
  intro p q hpq
  apply hFinj
  change (reesGradedSelfEquiv R I).symm (gradedReesPresentation R I z hz p) =
    (reesGradedSelfEquiv R I).symm (gradedReesPresentation R I z hz q)
  rw [hpq]

/-- Every member of a dimension-sized maximal-ideal generating family is regular.
This uses the graded presentation and Krull intersection, not a regular-sequence input. -/
theorem isSMulRegular_generator_of_span_eq_maximalIdeal
    {s : ℕ} (z : Fin (s + 1) → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (he : ringKrullDim R = s + 1) (i : Fin (s + 1)) : IsSMulRegular R (z i) :=
  isSMulRegular_generator_of_gradedReesPresentation_injective R (maximalIdeal R) z hz
    (gradedReesPresentation_injective_of_span_eq_maximalIdeal R z hz he)
    (maximalIdeal.isMaximal R).ne_top i

end Presentation

end SerrePositivity.HilbertSamuel
