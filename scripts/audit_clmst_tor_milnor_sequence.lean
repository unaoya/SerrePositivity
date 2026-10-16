import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTorExtension
import Mathlib.Util.AssertNoSorry

-- Actual coefficient-linear Milnor sequence and the full torsion-test implication.
assert_no_sorry SerrePositivity.algebraLinearMapOfScalarCommutation
assert_no_sorry SerrePositivity.algebraConjugateMap_scalar_commutation
assert_no_sorry SerrePositivity.algebraEquivariantShortComplex
assert_no_sorry SerrePositivity.algebraEquivariantShortComplex_restrictIso
assert_no_sorry SerrePositivity.algebraEquivariantShortComplex_shortExact
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelMap
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelMap_π
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelMap_transition
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelHolimMap
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelReconstruction_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientPowerCokernelReconstruction_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientPowerCokernelHolimIso
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientPowerCokernelHolimIso_naturality_left
assert_no_sorry SerrePositivity.DerivedCompletion.torAlgebraMilnorMiddleIso
assert_no_sorry SerrePositivity.DerivedCompletion.torAlgebraMilnorMiddleIso_scalar
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerCoefficientLift
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerCokernelMilnorScalarMap
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerCokernelTorAlgebraLimitComparison_scalar
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerCokernelTorAlgebraLimOneComparison_scalar
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerCokernelTorAlgebraLimOneIsoAt
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerCokernelTorAlgebraLimOneIsoAt_scalar
assert_no_sorry SerrePositivity.DerivedCompletion.torAlgebraMilnorShortComplex
assert_no_sorry SerrePositivity.DerivedCompletion.torAlgebraMilnorShortComplex_restrictIso
assert_no_sorry SerrePositivity.DerivedCompletion.torAlgebraMilnorShortComplex_shortExact
assert_no_sorry SerrePositivity.DerivedCompletion.torAlgebraMilnorShortComplexOver
assert_no_sorry SerrePositivity.DerivedCompletion.torAlgebraMilnorShortComplexOver_shortExact
assert_no_sorry SerrePositivity.DerivedCompletion.CompleteIdealExtensionClosed
assert_no_sorry SerrePositivity.DerivedCompletion.finite_tor_eq_zero_of_power_torsion_and_complete_extensions
assert_no_sorry SerrePositivity.DerivedCompletion.tor_eq_zero_of_power_torsion_and_complete_extensions
#print axioms SerrePositivity.algebraLinearMapOfScalarCommutation
#print axioms SerrePositivity.algebraConjugateMap_scalar_commutation
#print axioms SerrePositivity.algebraEquivariantShortComplex
#print axioms SerrePositivity.algebraEquivariantShortComplex_restrictIso
#print axioms SerrePositivity.algebraEquivariantShortComplex_shortExact
#print axioms SerrePositivity.DerivedCompletion.powerCokernelMap
#print axioms SerrePositivity.DerivedCompletion.powerCokernelMap_π
#print axioms SerrePositivity.DerivedCompletion.powerCokernelMap_transition
#print axioms SerrePositivity.DerivedCompletion.powerCokernelHolimMap
#print axioms SerrePositivity.DerivedCompletion.powerCokernelReconstruction_naturality
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientPowerCokernelReconstruction_quasiIso
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientPowerCokernelHolimIso
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientPowerCokernelHolimIso_naturality_left
#print axioms SerrePositivity.DerivedCompletion.torAlgebraMilnorMiddleIso
#print axioms SerrePositivity.DerivedCompletion.torAlgebraMilnorMiddleIso_scalar
#print axioms SerrePositivity.DerivedCompletion.modulePowerCoefficientLift
#print axioms SerrePositivity.DerivedCompletion.modulePowerCokernelMilnorScalarMap
#print axioms SerrePositivity.DerivedCompletion.modulePowerCokernelTorAlgebraLimitComparison_scalar
#print axioms SerrePositivity.DerivedCompletion.modulePowerCokernelTorAlgebraLimOneComparison_scalar
#print axioms SerrePositivity.DerivedCompletion.modulePowerCokernelTorAlgebraLimOneIsoAt
#print axioms SerrePositivity.DerivedCompletion.modulePowerCokernelTorAlgebraLimOneIsoAt_scalar
#print axioms SerrePositivity.DerivedCompletion.torAlgebraMilnorShortComplex
#print axioms SerrePositivity.DerivedCompletion.torAlgebraMilnorShortComplex_restrictIso
#print axioms SerrePositivity.DerivedCompletion.torAlgebraMilnorShortComplex_shortExact
#print axioms SerrePositivity.DerivedCompletion.torAlgebraMilnorShortComplexOver
#print axioms SerrePositivity.DerivedCompletion.torAlgebraMilnorShortComplexOver_shortExact
#print axioms SerrePositivity.DerivedCompletion.CompleteIdealExtensionClosed
#print axioms SerrePositivity.DerivedCompletion.finite_tor_eq_zero_of_power_torsion_and_complete_extensions
#print axioms SerrePositivity.DerivedCompletion.tor_eq_zero_of_power_torsion_and_complete_extensions

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R) [Module.Finite R M]
  (hC : IsModuleComplete R a (ModuleCat.of R C))

-- The actual algebra-valued Tor is the middle, including degree zero.
example (i : ℕ) : (torAlgebraMilnorShortComplex a C M hC i).X₂ =
    ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M := rfl

-- The preceding endpoint in Tor degree zero is lim¹ Tor_1, not a discarded term.
example : (torAlgebraMilnorShortComplex a C M hC 0).X₁ =
    modulePowerTorAlgebraLimOne a C M 1 := rfl

-- The arbitrary final test is neither required to be finite nor complete.
example (p : ℕ) (B : Type u) [CommRing B] (ψ : B →+* C) (I : Ideal B)
    (hc : IsModuleComplete R (p : R) (ModuleCat.of R C))
    (hExt : CompleteIdealExtensionClosed B (p : B) I)
    (hTor : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, (p : R) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ b ∈ I, torCoefficientScalarEndomorphism C N j (ψ b) = 0)
    (N : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (b : B) (hb : b ∈ I) :
    torCoefficientScalarEndomorphism C N i (ψ b) = 0 :=
  tor_eq_zero_of_power_torsion_and_complete_extensions p C B ψ I hc hExt hTor N i hi b hb
