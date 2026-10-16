import SerrePositivity.CLMST.Inputs.BasicSetup
import SerrePositivity.CLMST.PerfectoidIdealCompletedMul
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_quotientMap_surjective
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_quotient_isIntegralPerfectoid
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_completedQuotientMul_isIso
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_completeIdealExtensionClosed
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_mod_power_idempotent

#print axioms SerrePositivity.CLMST.perfectoidIdeal_quotientMap_surjective
#print axioms SerrePositivity.CLMST.perfectoidIdeal_quotient_isIntegralPerfectoid
#print axioms SerrePositivity.CLMST.perfectoidIdeal_completedQuotientMul_isIso
#print axioms SerrePositivity.CLMST.perfectoidIdeal_completeIdealExtensionClosed
#print axioms SerrePositivity.CLMST.perfectoidIdeal_mod_power_idempotent

assert_no_sorry SerrePositivity.CLMST.Inputs.perfectoidIdealMod_idempotent
#print axioms SerrePositivity.CLMST.Inputs.perfectoidIdealMod_idempotent

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.CLMST SerrePositivity.Section2
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

theorem audit_actual_completed_tower_ideal_mul
    (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A) :
    IsIso ((derivedComplexCompletionFunctor (CompletedTower A t p) (p : CompletedTower A t p)).map
      (boundedAboveDerivedAlgebraMul (R := CompletedTower A t p)
        ((CompletedTower A t p) ⧸ perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g))).hom) :=
  perfectoidIdeal_completedQuotientMul_isIso (CompletedTower A t p) p hperf
    (algebraMap A (CompletedTower A t p) g)

assert_no_sorry audit_actual_completed_tower_ideal_mul
#print axioms audit_actual_completed_tower_ideal_mul
