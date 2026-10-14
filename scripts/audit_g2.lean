import SerrePositivity.HomologicalAlgebra.DerivedTensorRealization
import SerrePositivity.HomologicalAlgebra.DerivedTensorBaseChange
import Mathlib.Util.AssertNoSorry

-- G2-1: every explicit public declaration, including the maps and natural comparisons.
assert_no_sorry SerrePositivity.chainDerivedRealization
assert_no_sorry SerrePositivity.extendChainHomologyIso
assert_no_sorry SerrePositivity.extendHomotopyChainHomologyIso
assert_no_sorry SerrePositivity.chainDerivedRealizationHomologyIso
assert_no_sorry SerrePositivity.chainHomologyZeroProjection
assert_no_sorry SerrePositivity.chainHomologyZeroProjection_naturality
assert_no_sorry SerrePositivity.chainHomologyZeroProjection_homology
assert_no_sorry SerrePositivity.chainHomologyZeroProjectionNatTrans
assert_no_sorry SerrePositivity.homotopyChainHomologyZeroProjection
assert_no_sorry SerrePositivity.homotopyChainSingleHomologyIso
assert_no_sorry SerrePositivity.homotopyChainHomologyZeroProjection_homology
assert_no_sorry SerrePositivity.chainDerivedRealizationComplexNatIso
assert_no_sorry SerrePositivity.extendChainSingleNatIso
assert_no_sorry SerrePositivity.chainDerivedRealizationSingleNatIso
assert_no_sorry SerrePositivity.chainDerivedAugmentation
assert_no_sorry SerrePositivity.chainDerivedAugmentation_homology_diagram
assert_no_sorry SerrePositivity.realizedSingleH0Iso
assert_no_sorry SerrePositivity.chainDerivedAugmentation_homology
assert_no_sorry SerrePositivity.chainDerivedRealization_homology_isZero_positive
assert_no_sorry SerrePositivity.realizedDerivedTensorFunctor
assert_no_sorry SerrePositivity.realizedDerivedTensorMapLeft
assert_no_sorry SerrePositivity.realizedDerivedTensorMapLeft_id
assert_no_sorry SerrePositivity.realizedDerivedTensorMapLeft_comp
assert_no_sorry SerrePositivity.realizedDerivedTensorH0NatIso
assert_no_sorry SerrePositivity.realizedDerivedTensorAugmentation
assert_no_sorry SerrePositivity.realizedDerivedTensor
assert_no_sorry SerrePositivity.realizedDerivedTensorHomologyIso
assert_no_sorry SerrePositivity.realizedDerivedTensorH0Iso
assert_no_sorry SerrePositivity.realizedDerivedTensorAugmentation_homology
assert_no_sorry SerrePositivity.realizedDerivedTensor_discrete_iff

open CategoryTheory CategoryTheory.Limits SerrePositivity
noncomputable section
attribute [local instance] HasDerivedCategory.standard

-- Arbitrary coefficient rings and modules: no flatness, finite generation, or regularity.
example (R M N : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (realizedDerivedTensor R M N) ≅ ModuleCat.of R (TensorProduct R M N) :=
  realizedDerivedTensorH0Iso R M N

-- Negative cohomological degrees, including degree zero, agree with the old Tor model.
example (R M N : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) (-(n : ℤ))).obj
      (realizedDerivedTensor R M N) ≅
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R M)).obj (ModuleCat.of R N) :=
  realizedDerivedTensorHomologyIso R M N n

-- The augmentation is a natural transformation with the actual derived-category target.
example (R : Type) [CommRing R] (M N N' : ModuleCat R) (f : N ⟶ N') :
    (realizedDerivedTensorFunctor R M).map f ≫
      (realizedDerivedTensorAugmentation R M).app N' =
    (realizedDerivedTensorAugmentation R M).app N ≫
      (((MonoidalCategory.tensoringLeft (ModuleCat R)).obj M) ⋙
        DerivedCategory.singleFunctor _ 0).map f :=
  (realizedDerivedTensorAugmentation R M).naturality f

#print axioms SerrePositivity.realizedDerivedTensorH0Iso
#print axioms SerrePositivity.realizedDerivedTensorAugmentation_homology
#print axioms SerrePositivity.realizedDerivedTensor_discrete_iff

-- G2-2a: the module-valued input to the general base-change construction.
assert_no_sorry SerrePositivity.extendRestrictTensorIso
assert_no_sorry SerrePositivity.restrictChainHomologyIso
assert_no_sorry SerrePositivity.restrictHomotopyChainHomologyIso
assert_no_sorry SerrePositivity.restrictDerivedBaseChangeHomotopyIso
assert_no_sorry SerrePositivity.derivedModuleBaseChange
assert_no_sorry SerrePositivity.derivedModuleBaseChangeHomologyIso
assert_no_sorry SerrePositivity.derivedModuleBaseChangeTorIso
assert_no_sorry SerrePositivity.derivedModuleBaseChange_negative_homology_vanishes_iff
assert_no_sorry SerrePositivity.derivedModuleBaseChangeH0Iso
assert_no_sorry SerrePositivity.derivedModuleBaseChangeAugmentation
assert_no_sorry SerrePositivity.derivedModuleBaseChangeAugmentation_homology
assert_no_sorry SerrePositivity.derivedModuleBaseChangeResolutionIso
assert_no_sorry SerrePositivity.derivedModuleBaseChangeResolutionIso_naturality
assert_no_sorry SerrePositivity.derivedModuleBaseChange_homology_isZero_positive

-- Quotient maps are permitted; no regularity or flatness of the quotient is assumed.
example (R : Type) [CommRing R] (J : Ideal R) (M : ModuleCat R) :
    (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ J)) 0).obj
      ((derivedModuleBaseChange (Ideal.Quotient.mk J)).obj M) ≅
      (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj M :=
  (derivedModuleBaseChangeH0Iso (Ideal.Quotient.mk J)).app M

#print axioms SerrePositivity.derivedModuleBaseChangeTorIso
#print axioms SerrePositivity.derivedModuleBaseChangeResolutionIso_naturality
