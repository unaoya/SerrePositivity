import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerIsoMapCompatibility
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTensorHolim
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteCoefficientPowerHolim
import Mathlib.Util.AssertNoSorry

-- KL-A2e: the original ordinary-quotient tower and its reconstruction.
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitMap_eq_iso_hom
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerCompatibleLift_iso
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensorTower
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensorTransition
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensorReductionMap_transition
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensorReconstruction
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensorReconstruction_projection
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerCokernelHolimIso
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelReconstruction_comp_modulePowerHolimIso
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensorReconstruction_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerDerivedTensorHolimComplex
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerDerivedTensorHolimProjection
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientPowerReconstruction_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientPowerHolimIso
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientPowerHolimIso_projection
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitMap_eq_iso_hom
#print axioms SerrePositivity.DerivedCompletion.complexTowerCompatibleLift_iso
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensorTower
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensorTransition
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensorReductionMap_transition
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensorReconstruction
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensorReconstruction_projection
#print axioms SerrePositivity.DerivedCompletion.modulePowerCokernelHolimIso
#print axioms SerrePositivity.DerivedCompletion.powerCokernelReconstruction_comp_modulePowerHolimIso
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensorReconstruction_quasiIso
#print axioms SerrePositivity.DerivedCompletion.modulePowerDerivedTensorHolimComplex
#print axioms SerrePositivity.DerivedCompletion.modulePowerDerivedTensorHolimProjection
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientPowerReconstruction_quasiIso
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientPowerHolimIso
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientPowerHolimIso_projection

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] [IsRegularLocalRing R]
  (a : R) (C M : ModuleCat.{u} R) [Module.Finite R M] (hC : IsModuleComplete R a C)

-- No flatness or completeness assumption on the finite test module.
example : (boundedAboveDerivedTensorModuleFunctor C).obj M ≅
    DerivedCategory.Q.obj (modulePowerDerivedTensorHolimComplex R a C M) :=
  finiteCoefficientPowerHolimIso R a C M hC

-- The original map to every ordinary quotient, including exponent zero.
example (n : ℕ) :
    (finiteCoefficientPowerHolimIso R a C M hC).hom ≫
      modulePowerDerivedTensorHolimProjection R a C M n =
        (boundedAboveDerivedTensorModuleFunctor C).map (modulePowerReductionMap a M n) :=
  finiteCoefficientPowerHolimIso_projection R a C M hC n
