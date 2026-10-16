import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeAugmentationModels
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.mappedProjectiveResolutionAugmentation
assert_no_sorry SerrePositivity.mappedProjectiveResolutionAugmentation_eq_projection
assert_no_sorry SerrePositivity.mappedProjectiveResolutionAugmentation_eq_map
assert_no_sorry SerrePositivity.mapExtendIso_single_comparison
assert_no_sorry SerrePositivity.mapExtendIso_resolution_augmentation
assert_no_sorry SerrePositivity.derivedModuleBaseChangeAugmentation_resolution_homotopy
assert_no_sorry SerrePositivity.derivedModuleBaseChangeResolutionIso_augmentation
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeModuleAugmentation_chosen_models
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeModuleAugmentation_projective_models

#print axioms SerrePositivity.mappedProjectiveResolutionAugmentation
#print axioms SerrePositivity.mappedProjectiveResolutionAugmentation_eq_projection
#print axioms SerrePositivity.mappedProjectiveResolutionAugmentation_eq_map
#print axioms SerrePositivity.mapExtendIso_single_comparison
#print axioms SerrePositivity.mapExtendIso_resolution_augmentation
#print axioms SerrePositivity.derivedModuleBaseChangeAugmentation_resolution_homotopy
#print axioms SerrePositivity.derivedModuleBaseChangeResolutionIso_augmentation
#print axioms SerrePositivity.boundedAboveDerivedBaseChangeModuleAugmentation_chosen_models
#print axioms SerrePositivity.boundedAboveDerivedBaseChangeModuleAugmentation_projective_models

noncomputable section
universe u
open CategoryTheory SerrePositivity
attribute [local instance] HasDerivedCategory.standard

-- An arbitrary quotient, with no flatness, regularity or Tor hypothesis.
example (R : Type u) [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (P : BoundedAboveDerivedModel (boundedAboveDerivedSingleFunctor.obj M).obj)
    (ε : P.complex ⟶ cochainSingleZero M) (hε : DerivedCategory.Q.map ε = P.iso.hom) :
    (boundedAboveDerivedBaseChangeModuleAugmentation (Ideal.Quotient.mk I)).app M =
      (boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk I)
        (boundedAboveDerivedSingleFunctor.obj M) P).hom ≫
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex (.up ℤ)).map ε ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (.up ℤ) 0).hom.app M) :=
  boundedAboveDerivedBaseChangeModuleAugmentation_projective_models _ P ε hε

-- A functor in the opposite coefficient direction is also supported by the generalized API.
example (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S)
    (M : ModuleCat.{u} S) (P : ProjectiveResolution M) :
    (mapExtendIso (ModuleCat.restrictScalars φ) P.complex embUp).hom ≫
        HomologicalComplex.extendMap
          (mappedProjectiveResolutionAugmentation (ModuleCat.restrictScalars φ) P) embUp ≫
        (extendChainSingleNatIso R).hom.app ((ModuleCat.restrictScalars φ).obj M) =
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
          (projectiveResolutionCochainAugmentation P) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.restrictScalars φ) (.up ℤ) 0).hom.app M :=
  mapExtendIso_resolution_augmentation _ P
