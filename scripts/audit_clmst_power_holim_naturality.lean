import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerHolimNaturality
import Mathlib.Util.AssertNoSorry

-- KL-A2f: original reconstruction is natural for coefficient morphisms.
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitLift_precomp
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerCompatibleLift_precomp
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerCompatibleLift_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensorTransition_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensorHolimMap
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensorReconstruction_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerDerivedTensorHolimMap
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientPowerHolimIso_naturality_left
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitLift_precomp
#print axioms SerrePositivity.DerivedCompletion.complexTowerCompatibleLift_precomp
#print axioms SerrePositivity.DerivedCompletion.complexTowerCompatibleLift_naturality
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensorTransition_naturality
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensorHolimMap
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensorReconstruction_naturality
#print axioms SerrePositivity.DerivedCompletion.modulePowerDerivedTensorHolimMap
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientPowerHolimIso_naturality_left

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R) [Module.Finite R M]
  (hC : IsModuleComplete R a (ModuleCat.of R C))

-- An arbitrary coefficient-ring scalar, not necessarily coming from the base ring.
example (c : C) :
    let f := ModuleCat.ofHom (LinearMap.mulLeft R c)
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom ≫
        (finiteCoefficientPowerHolimIso R a (ModuleCat.of R C) M hC).hom =
      (finiteCoefficientPowerHolimIso R a (ModuleCat.of R C) M hC).hom ≫
        modulePowerDerivedTensorHolimMap a M f :=
  finiteCoefficientPowerHolimIso_naturality_left a M
    (ModuleCat.ofHom (LinearMap.mulLeft R c)) hC hC
