import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeAugmentationComparison
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
open CategoryTheory SerrePositivity MonoidalCategory
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

assert_no_sorry SerrePositivity.cochainTensorBaseChangeIso_single
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeModuleAugmentation_map_model
assert_no_sorry SerrePositivity.cochainTensorBaseChangeIso_augmentation
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeModelIso_chosen_hom
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorModelIso_chosen_hom
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeSingleModel
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeSingleModel_augmentation
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorBaseChangeModuleIso_augmentation

#print axioms SerrePositivity.cochainTensorBaseChangeIso_single
#print axioms SerrePositivity.boundedAboveDerivedBaseChangeModuleAugmentation_map_model
#print axioms SerrePositivity.cochainTensorBaseChangeIso_augmentation
#print axioms SerrePositivity.boundedAboveDerivedBaseChangeModelIso_chosen_hom
#print axioms SerrePositivity.boundedAboveDerivedTensorModelIso_chosen_hom
#print axioms SerrePositivity.boundedAboveDerivedBaseChangeSingleModel
#print axioms SerrePositivity.boundedAboveDerivedBaseChangeSingleModel_augmentation
#print axioms SerrePositivity.boundedAboveDerivedTensorBaseChangeModuleIso_augmentation

-- Only scalar-extension Tor conditions on the two factors; no Tor independence between them.
example (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S)
    (M N : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing φ M) (hN : scalarExtensionTorVanishing φ N) :
    (boundedAboveDerivedTensorBaseChangeModuleIso φ M N hM hN).hom.hom ≫
        (boundedAboveDerivedTensorModuleAugmentation ((ModuleCat.extendScalars φ).obj M)).app
          ((ModuleCat.extendScalars φ).obj N) =
      ((boundedAboveDerivedBaseChange φ).map
        (ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation M).app N))).hom ≫
        (boundedAboveDerivedBaseChangeModuleAugmentation φ).app (M ⊗ N) ≫
        (DerivedCategory.singleFunctor (ModuleCat S) 0).map
          (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ) M N) :=
  boundedAboveDerivedTensorBaseChangeModuleIso_augmentation φ M N hM hN
