module
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidCompletedTensorDiscrete
public import SerrePositivity.CommutativeAlgebra.PerfectoidDerivedComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedSurjectiveAlgebraMul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedQuotientTensorExtension

/-! # The original completed multiplication for perfectoid quotients -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]

/-- A surjective morphism of integral perfectoid rings has invertible completed derived product. -/
lemma integralPerfectoid_completedSurjectiveAlgebraMul_isIso
    (A : Type u) [CommRing A] [Algebra R A]
    (hR : IsIntegralPerfectoid R p) (hA : IsIntegralPerfectoid A p)
    (hs : Function.Surjective (algebraMap R A)) :
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (boundedAboveDerivedAlgebraMul (R := R) A).hom) :=
  completedSurjectiveAlgebraMul_isIso R (p : R) A hs
    (hA.isModuleComplete_algebra R A p)
    (integralPerfectoid_completedTensor_pure p R A A hR hA hA)

/-- The map is exactly the original multiplication on the original perfectoid quotient. -/
lemma integralPerfectoid_completedQuotientMul_isIso (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) :
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom) :=
  integralPerfectoid_completedSurjectiveAlgebraMul_isIso p R (R ⧸ I) hR hQ
    Ideal.Quotient.mk_surjective

/-- Complete I-almost zero modules are extension closed for this same quotient ideal. -/
lemma integralPerfectoid_completeIdealExtensionClosed (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) :
    CompleteIdealExtensionClosed R (p : R) I :=
  completeIdealExtensionClosed_of_completed_quotient_mul_isIso (p : R) I
    (integralPerfectoid_completedQuotientMul_isIso p R I hR hQ)

/-- Every original p-power quotient image of I is idempotent, including exponent zero. -/
lemma integralPerfectoid_ideal_mod_power_idempotent (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) (n : ℕ) :
    IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}))) :=
  ideal_mod_power_idempotent_of_completed_quotient_mul_isIso (p : R) I
    (integralPerfectoid_completedQuotientMul_isIso p R I hR hQ) n

end SerrePositivity.BhattScholze
