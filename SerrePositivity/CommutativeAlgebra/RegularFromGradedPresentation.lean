module

public import SerrePositivity.CommutativeAlgebra.GradedRegularLift
public import SerrePositivity.CommutativeAlgebra.GradedReesSelf
public import SerrePositivity.CommutativeAlgebra.HilbertSamuelPolynomial

/-!
# Regular generators from an injective associated graded presentation

When the presentation of `gr_I(R)` by the polynomial algebra on generators of
`I` is injective, every polynomial variable acts regularly on the associated
graded ring. The self associated graded module then transports this regularity
to each degree, and Krull intersection lifts it to the original ring.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSamuel

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

/-- The Samuel function has the exact first-difference formula for each
generator of an injective associated graded presentation. -/
theorem samuelFunction_succ_eq_add_generator_quotient_of_gradedReesPresentation_injective
    (i : Fin s) (n : ℕ) :
    samuelFunction R I R (n + 1) = samuelFunction R I R n +
      samuelFunction R I (QuotSMulTop (z i) R) (n + 1) :=
  samuelFunction_succ_eq_add_quotSMulTop_of_gradedMultiplication_injective I
    ⟨z i, hz ▸ Ideal.subset_span (Set.mem_range_self i)⟩
    (gradedMultiplication_injective_of_gradedReesPresentation_injective R I z hz hinj i) n

end SerrePositivity.HilbertSamuel
