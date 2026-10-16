import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedQuotientTensorExtension
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.cochain_homology_smul_surjective_of_koszul_map_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.boundedAbove_homology_smul_surjective_of_completion_map_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.quotientTorOne_smul_surjective_of_completed_mul_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.completeIdealExtensionClosed_of_completed_quotient_mul_isIso
#print axioms SerrePositivity.DerivedCompletion.cochain_homology_smul_surjective_of_koszul_map_quasiIso
#print axioms SerrePositivity.DerivedCompletion.boundedAbove_homology_smul_surjective_of_completion_map_isIso
#print axioms SerrePositivity.DerivedCompletion.quotientTorOne_smul_surjective_of_completed_mul_isIso
#print axioms SerrePositivity.DerivedCompletion.completeIdealExtensionClosed_of_completed_quotient_mul_isIso

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

-- The hypothesis is about the existing standard multiplication itself.
example (R : Type u) [CommRing R] (a : R) (I : Ideal R)
    (hμ : IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)) :
    CompleteIdealExtensionClosed R a I :=
  completeIdealExtensionClosed_of_completed_quotient_mul_isIso a I hμ

-- Divisibility is obtained on the original standard quotient Tor, over any ring.
example (R : Type u) [CommRing R] (a : R) (I : Ideal R)
    (hμ : IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)) :
    Function.Surjective (fun x : TorModule R 1 (R ⧸ I) (R ⧸ I) => a • x) :=
  quotientTorOne_smul_surjective_of_completed_mul_isIso a I hμ

assert_no_sorry SerrePositivity.ideal_mod_power_idempotent_of_conormal_surjective
#print axioms SerrePositivity.ideal_mod_power_idempotent_of_conormal_surjective
assert_no_sorry SerrePositivity.DerivedCompletion.ideal_mod_power_idempotent_of_completed_quotient_mul_isIso
#print axioms SerrePositivity.DerivedCompletion.ideal_mod_power_idempotent_of_completed_quotient_mul_isIso

-- The ordinary ideal image is computed with the original quotient map, all n.
example (R : Type u) [CommRing R] (a : R) (I : Ideal R)
    (hμ : IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)) (n : ℕ) :
    IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))) :=
  ideal_mod_power_idempotent_of_completed_quotient_mul_isIso a I hμ n
