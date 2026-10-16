import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedSurjectiveAlgebraMul
import SerrePositivity.BhattScholze.PerfectoidCompletedQuotientMul
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.surjectiveAlgebraMul_h0_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.completedSurjectiveAlgebraMul_isIso
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedSurjectiveAlgebraMul_isIso
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedQuotientMul_isIso
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completeIdealExtensionClosed
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_ideal_mod_power_idempotent

#print axioms SerrePositivity.DerivedCompletion.surjectiveAlgebraMul_h0_isIso
#print axioms SerrePositivity.DerivedCompletion.completedSurjectiveAlgebraMul_isIso
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedSurjectiveAlgebraMul_isIso
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedQuotientMul_isIso
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completeIdealExtensionClosed
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_ideal_mod_power_idempotent

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard

theorem audit_actual_zero_quotient_completed_mul (p : ℕ) [Fact p.Prime]
    (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p) :
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ (⊤ : Ideal R))).hom) :=
  integralPerfectoid_completedQuotientMul_isIso p R ⊤ hR (Or.inl inferInstance)

assert_no_sorry audit_actual_zero_quotient_completed_mul
#print axioms audit_actual_zero_quotient_completed_mul
