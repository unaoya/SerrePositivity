import SerrePositivity.HomologicalAlgebra.DerivedTensorRealization
import SerrePositivity.HomologicalAlgebra.DerivedTensorBaseChange
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionNaturality
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

-- G2-3a: arbitrary complexes, including unbounded and nonprojective ones.
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulStage
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulTransition
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulTransition_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulProductFunctor
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulDifferenceFunctor
assert_no_sorry SerrePositivity.DerivedCompletion.cochainMappingConeFunctor
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionFunctor
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionObject
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulStage_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionObject_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulInclusion_compatible
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionUnit
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionUnit_comp_projection
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionUnitObject

open SerrePositivity.DerivedCompletion

-- No regularity of a or termwise completeness of K is assumed, also at n = 0.
example (R : Type) [CommRing R] (a : R) (K : CochainComplex (ModuleCat R) ℤ) :
    IsComplete R a (complexCompletionObject R a K) :=
  complexCompletionObject_isComplete R a K

example (R : Type) [CommRing R] (a : R) (K : CochainComplex (ModuleCat R) ℤ) :
    complexCompletionUnit R a K ≫
      complexTowerProjection R (complexPowerKoszulStage R a K)
        (complexPowerKoszulTransition R a K) ≫
          CategoryTheory.Limits.Pi.π (complexPowerKoszulStage R a K) 0 =
            CochainComplex.mappingCone.inr (smulId (a ^ 0) K) :=
  complexCompletionUnit_comp_projection R a K 0

#print axioms SerrePositivity.DerivedCompletion.complexCompletionObject_isComplete
#print axioms SerrePositivity.DerivedCompletion.complexCompletionUnit_comp_projection

-- G2-3b, first part: quasi-isomorphism invariance and the actual derived functor and unit.
assert_no_sorry SerrePositivity.DerivedCompletion.cochainMappingConeFunctor_map_eq
assert_no_sorry SerrePositivity.DerivedCompletion.cochainMappingConeFunctor_inl
assert_no_sorry SerrePositivity.DerivedCompletion.cochainMappingConeFunctor_map_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerProductMap_homology
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerProductMap_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.scalarConeFunctor_map_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionFunctor_map_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionFunctor_inverts_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.derivedComplexCompletionFunctor
assert_no_sorry SerrePositivity.DerivedCompletion.derivedComplexCompletionComparison
assert_no_sorry SerrePositivity.DerivedCompletion.derivedComplexCompletionComparison_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.derivedComplexCompletionFunctor_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulProductInclusion_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionUnit_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionUnitNatTrans
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionUnitDerivedInput
assert_no_sorry SerrePositivity.DerivedCompletion.derivedComplexCompletionUnit
assert_no_sorry SerrePositivity.DerivedCompletion.derivedComplexCompletionUnit_comparison

-- The output and unit live in the actual derived category, for every derived object.
example (R : Type) [CommRing R] (a : R) (X : ConcreteDerivedCategory R) :
    IsComplete R a ((derivedComplexCompletionFunctor R a).obj X) :=
  derivedComplexCompletionFunctor_isComplete R a X

example (R : Type) [CommRing R] (a : R) {X Y : ConcreteDerivedCategory R} (f : X ⟶ Y) :
    f ≫ (derivedComplexCompletionUnit R a).app Y =
      (derivedComplexCompletionUnit R a).app X ≫ (derivedComplexCompletionFunctor R a).map f :=
  (derivedComplexCompletionUnit R a).naturality f

example (R : Type) [CommRing R] (a : R) (K : CochainComplex (ModuleCat R) ℤ) :
    (derivedComplexCompletionUnit R a).app (DerivedCategory.Q.obj K) ≫
      (derivedComplexCompletionComparison R a).hom.app K =
        DerivedCategory.Q.map (complexCompletionUnit R a K) :=
  derivedComplexCompletionUnit_comparison R a K

#print axioms SerrePositivity.DerivedCompletion.complexCompletionFunctor_map_quasiIso
#print axioms SerrePositivity.DerivedCompletion.derivedComplexCompletionFunctor_isComplete
#print axioms SerrePositivity.DerivedCompletion.derivedComplexCompletionUnit_comparison
