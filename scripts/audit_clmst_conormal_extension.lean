import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTorConormal
import SerrePositivity.HomologicalAlgebra.PerfectQuotientTorOne
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.linearMap_eq_zero_of_smul_surjective_of_isModuleComplete
assert_no_sorry SerrePositivity.DerivedCompletion.ideal_annihilates_of_square_annihilates_of_conormal_surjective
assert_no_sorry SerrePositivity.DerivedCompletion.completeIdealExtensionClosed_of_conormal_surjective
assert_no_sorry SerrePositivity.DerivedCompletion.completeIdealExtensionClosed_of_quotientTorOne_surjective
assert_no_sorry SerrePositivity.DerivedCompletion.completeIdealExtensionClosed_of_quotientDerivedTensor_homology_surjective
assert_no_sorry SerrePositivity.DerivedCompletion.tor_eq_zero_of_power_torsion_and_quotientTorOne
assert_no_sorry SerrePositivity.DerivedCompletion.tor_eq_zero_of_power_torsion_and_conormal
assert_no_sorry SerrePositivity.idealSubtype_lTensor_quotient_eq_zero
assert_no_sorry SerrePositivity.quotientTorOneConormalEquiv
assert_no_sorry SerrePositivity.quotientTorOne_smul_surjective_iff_conormal
assert_no_sorry SerrePositivity.quotientTorOne_subsingleton_iff_idempotent
assert_no_sorry SerrePositivity.radicalIdeal_idempotent_of_power_surjective
assert_no_sorry SerrePositivity.radicalIdeal_idempotent_of_perfectRing
assert_no_sorry SerrePositivity.radicalIdeal_cotangent_subsingleton_of_perfectRing
assert_no_sorry SerrePositivity.radicalIdeal_quotientTorOne_subsingleton
#print axioms SerrePositivity.DerivedCompletion.linearMap_eq_zero_of_smul_surjective_of_isModuleComplete
#print axioms SerrePositivity.DerivedCompletion.ideal_annihilates_of_square_annihilates_of_conormal_surjective
#print axioms SerrePositivity.DerivedCompletion.completeIdealExtensionClosed_of_conormal_surjective
#print axioms SerrePositivity.DerivedCompletion.completeIdealExtensionClosed_of_quotientTorOne_surjective
#print axioms SerrePositivity.DerivedCompletion.completeIdealExtensionClosed_of_quotientDerivedTensor_homology_surjective
#print axioms SerrePositivity.DerivedCompletion.tor_eq_zero_of_power_torsion_and_quotientTorOne
#print axioms SerrePositivity.DerivedCompletion.tor_eq_zero_of_power_torsion_and_conormal
#print axioms SerrePositivity.idealSubtype_lTensor_quotient_eq_zero
#print axioms SerrePositivity.quotientTorOneConormalEquiv
#print axioms SerrePositivity.quotientTorOne_smul_surjective_iff_conormal
#print axioms SerrePositivity.quotientTorOne_subsingleton_iff_idempotent
#print axioms SerrePositivity.radicalIdeal_idempotent_of_power_surjective
#print axioms SerrePositivity.radicalIdeal_idempotent_of_perfectRing
#print axioms SerrePositivity.radicalIdeal_cotangent_subsingleton_of_perfectRing
#print axioms SerrePositivity.radicalIdeal_quotientTorOne_subsingleton

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion

-- Actual conormal criterion, without regularity or separation assumptions.
example (R : Type u) [CommRing R] (a : R) (I : Ideal R)
    (h : Function.Surjective (fun x : I.Cotangent => a • x)) :
    CompleteIdealExtensionClosed R a I :=
  completeIdealExtensionClosed_of_conormal_surjective a I h

-- The first Tor comparison uses the original quotient in both variables.
example (R : Type u) [CommRing R] (I : Ideal R) :
    TorModule R 1 (R ⧸ I) (R ⧸ I) ≃ₗ[R] I.Cotangent :=
  quotientTorOneConormalEquiv R I

-- Final tests range over arbitrary modules, not only complete or finite ones.
example {R : Type u} [CommRing R] [IsRegularLocalRing R] (p : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]
    (B : Type u) [CommRing B] (ψ : B →+* C) (I : Ideal B)
    (hC : IsModuleComplete R (p : R) (ModuleCat.of R C))
    (hTor : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, (p : R) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
      ∀ b ∈ I, torCoefficientScalarEndomorphism C N j (ψ b) = 0)
    (hQ : Function.Surjective
      (fun x : TorModule B 1 (B ⧸ I) (B ⧸ I) => (p : B) • x))
    (N : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (b : B) (hb : b ∈ I) :
    torCoefficientScalarEndomorphism C N i (ψ b) = 0 :=
  tor_eq_zero_of_power_torsion_and_quotientTorOne p C B ψ I hC hTor hQ N i hi b hb
