module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuelDimension
public import SerrePositivity.CommutativeAlgebra.HomogeneousRelationGrowth
public import SerrePositivity.CommutativeAlgebra.GradedPresentationMap
public import SerrePositivity.CommutativeAlgebra.SamuelCumulative
public import SerrePositivity.CommutativeAlgebra.RegularFromGradedPresentation

/-! # Minimal maximal-ideal generators have a free associated graded presentation

If a nonzero homogeneous relation existed, the cumulative Hilbert growth would
have degree below the number of generators. The Samuel dimension theorem rules
this out when that number equals the ring dimension.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSamuel

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
  have hker := ker_isHomogeneous_of_degree_preserving NS NT F hdegree
  have hfinite : ∀ n, IsFiniteLength R (NS n) := by
    intro n
    apply Module.length_ne_top_iff.mp
    rw [homogeneousSubmodule_length_restrictScalars]
    exact Module.length_ne_top_iff.mpr
      (PolynomialHilbertSeries.finiteLength_homogeneousSubmodule k (Fin (s + 1)) n)
  have hseries : lengthSeries NS = (PowerSeries.invOneSubPow ℚ (s + 1)).val := by
    rw [← PolynomialHilbertSeries.lengthSeries_homogeneousSubmodule k (s + 1)]
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
    have hbound := HomogeneousRelationGrowth.natDegree_le_of_relation NS NT F
      (gradedPresentationMap_surjective R I z hz) hdegree f hd d
      (fun n x hx => by
        change x.IsHomogeneous n at hx
        change (f * x).IsHomogeneous (n + d)
        simpa only [Nat.add_comm] using hfhom.mul hx)
      hrelation hfinite s hseries (poly R I R) (hP.leadingCoeff_pos R hI) hcumulative
    have hdim : (poly R I R).natDegree = s + 1 := by
      rw [natDegree_poly_eq_dim R I hI]
      exact_mod_cast (PrimaryParameterExistence.natCast_dimToNat R).trans he
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

end SerrePositivity.HilbertSamuel
