import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange
import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedUnit
import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedAssociator
import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedTensor
import SerrePositivity.HomologicalAlgebra.BoundedAboveTensorFunctor
import SerrePositivity.HomologicalAlgebra.BoundedAboveTensorModels
import SerrePositivity.PerfectComplex.TensorBoundedAbove
import SerrePositivity.HomologicalAlgebra.DerivedTensorRealization
import SerrePositivity.HomologicalAlgebra.DerivedTensorBaseChange
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionNaturality
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ConstantTower
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.LocalizationResolution
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.LocalizationHomCoordinates
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.LocalizationTowerComparison
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerExact
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ConeShortExact
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReconstruction
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

-- G2-3b-ii, preparation: reconstruct every complex from the identity-transition tower.
assert_no_sorry SerrePositivity.DerivedCompletion.constantComplexTower
assert_no_sorry SerrePositivity.DerivedCompletion.constantComplexTowerUnit
assert_no_sorry SerrePositivity.DerivedCompletion.constantComplexTowerUnit_comp_projection
assert_no_sorry SerrePositivity.DerivedCompletion.constantComplexTowerHomologyDifference_surjective
assert_no_sorry SerrePositivity.DerivedCompletion.constantComplexTowerUnit_boundary
assert_no_sorry SerrePositivity.DerivedCompletion.constantComplexTowerUnit_homology_bijective
assert_no_sorry SerrePositivity.DerivedCompletion.constantComplexTowerUnit_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.constantComplexTowerUnitIso
assert_no_sorry SerrePositivity.DerivedCompletion.constantComplexTowerUnitIso_inv

-- Reconstruction uses the standard diagonal map and the actual degree-zero projection.
example (R : Type) [CommRing R] (K : CochainComplex (ModuleCat R) ℤ) :
    DerivedCategory.Q.obj K ≅ complexTowerHomotopyLimitObject R
      (constantComplexTower R K) (fun _ ↦ 𝟙 K) :=
  constantComplexTowerUnitIso R K

example (R : Type) [CommRing R] (K : CochainComplex (ModuleCat R) ℤ) :
    (constantComplexTowerUnitIso R K).inv =
      DerivedCategory.Q.map
        (complexTowerProjection R (constantComplexTower R K) (fun _ ↦ 𝟙 K) ≫
          CategoryTheory.Limits.Pi.π (constantComplexTower R K) 0) :=
  constantComplexTowerUnitIso_inv R K

#print axioms SerrePositivity.DerivedCompletion.constantComplexTowerUnit_quasiIso
#print axioms SerrePositivity.DerivedCompletion.constantComplexTowerUnitIso_inv

-- The length-one free telescope resolution and the complete-object vanishing criterion.
assert_no_sorry SerrePositivity.DerivedCompletion.localizationPresentationComplex
assert_no_sorry SerrePositivity.DerivedCompletion.localizationPresentationComplex_shortExact
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionComplex
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionComplex_isStrictlyLE
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionComplex_projective
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionComplex_isKProjective
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionAugmentation
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionAugmentation_quasiIso
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionDerivedIso
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionHomologyEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionHomology_subsingleton
assert_no_sorry SerrePositivity.DerivedCompletion.isComplete_iff_localizationResolutionHomology_subsingleton
assert_no_sorry SerrePositivity.DerivedCompletion.isComplete_iff_localizationResolutionHom_acyclic

-- This is the original IsComplete condition, for arbitrary unbounded complexes and zero divisors.
example (R : Type) [CommRing R] (a : R) (K : CochainComplex (ModuleCat R) ℤ) :
    IsComplete R a (DerivedCategory.Q.obj K) ↔
      (CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K).Acyclic :=
  isComplete_iff_localizationResolutionHom_acyclic R a K

example (R : Type) [CommRing R] (a : R) :
    (localizationResolutionComplex R a).IsKProjective := inferInstance

#print axioms SerrePositivity.DerivedCompletion.localizationResolutionHomologyEquiv
#print axioms SerrePositivity.DerivedCompletion.isComplete_iff_localizationResolutionHom_acyclic

-- Coordinates of the telescope Hom complex, including the signed differential.
assert_no_sorry SerrePositivity.mappingConeSourceCochainEquiv
assert_no_sorry SerrePositivity.mappingConeSourceCochainEquiv_symm_apply
assert_no_sorry SerrePositivity.mappingConeSourceCochainEquiv_symm_δ
assert_no_sorry SerrePositivity.DerivedCompletion.localizationFreeCochainEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.localizationFreeCochainEquiv_fromSingleMk
assert_no_sorry SerrePositivity.DerivedCompletion.localizationFreeCochainEquiv_δ
assert_no_sorry SerrePositivity.DerivedCompletion.localizationFreeCochainEquiv_precomp
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionCochainEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionCochainEquiv_symm_apply
assert_no_sorry SerrePositivity.DerivedCompletion.localizationResolutionCochainEquiv_symm_δ

example (R : Type) [CommRing R] (a : R) (K : CochainComplex (ModuleCat R) ℤ) :
    CochainComplex.HomComplex.Cochain (localizationResolutionComplex R a) K 0 ≃ₗ[R]
      (ℕ → K.X (-1)) × (ℕ → K.X 0) :=
  localizationResolutionCochainEquiv R a K (-1) 0 (by norm_num)

#print axioms SerrePositivity.DerivedCompletion.localizationResolutionCochainEquiv_symm_δ

-- The residual scalar-transition tower is the actual telescope Hom complex.
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitDegreeEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitDegreeEquiv_fst
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitDegreeEquiv_snd
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitDegreeIso_d
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitDegreeEquiv_d_fst
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitDegreeEquiv_d_snd
assert_no_sorry SerrePositivity.DerivedCompletion.scalarComplexTowerHomotopyLimit
assert_no_sorry SerrePositivity.DerivedCompletion.localizationHomTowerDegreeEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.localizationHomTowerDegreeEquiv_coordinates
assert_no_sorry SerrePositivity.DerivedCompletion.localizationHomTowerDegreeEquiv_d
assert_no_sorry SerrePositivity.DerivedCompletion.localizationHomTowerIso
assert_no_sorry SerrePositivity.DerivedCompletion.scalarComplexTowerHomotopyLimit_acyclic_of_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.isComplete_iff_scalarComplexTowerHomotopyLimit_acyclic
assert_no_sorry SerrePositivity.DerivedCompletion.scalarComplexTowerHomotopyLimitObject_isZero_of_isComplete

-- The criterion includes unbounded complexes and does not assume any lim-one vanishing.
example (R : Type) [CommRing R] (a : R) (K : CochainComplex (ModuleCat R) ℤ) :
    IsComplete R a (DerivedCategory.Q.obj K) ↔
      (scalarComplexTowerHomotopyLimit R a K).Acyclic :=
  isComplete_iff_scalarComplexTowerHomotopyLimit_acyclic R a K

example (R : Type) [CommRing R] (a : R) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    IsZero (DerivedCategory.Q.obj (scalarComplexTowerHomotopyLimit R a K)) :=
  scalarComplexTowerHomotopyLimitObject_isZero_of_isComplete R a K hK

#print axioms SerrePositivity.DerivedCompletion.localizationHomTowerIso
#print axioms SerrePositivity.DerivedCompletion.scalarComplexTowerHomotopyLimitObject_isZero_of_isComplete

-- Arbitrary tower maps, compatibility with the standard lifts, and short exactness of holim.
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerDifferenceArrowMap
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitMap
assert_no_sorry SerrePositivity.DerivedCompletion.complexProductDegreeEquiv_map
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitDegreeIso_map
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitDegreeEquiv_map_fst
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitDegreeEquiv_map_snd
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitLift_map
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerCompatibleLift_map
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitMap_comp_zero
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitShortComplex
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitShortComplex_shortExact
assert_no_sorry SerrePositivity.DerivedCompletion.coneStandardProjection
assert_no_sorry SerrePositivity.DerivedCompletion.coneStandardProjection_inl
assert_no_sorry SerrePositivity.DerivedCompletion.coneStandardProjection_inr
assert_no_sorry SerrePositivity.DerivedCompletion.coneStandardShortComplex
assert_no_sorry SerrePositivity.DerivedCompletion.coneStandardShortComplexSplitting
assert_no_sorry SerrePositivity.DerivedCompletion.coneStandardShortComplex_shortExact

-- The stagewise exact sequence uses the actual shifted source, for every cochain map.
example (R : Type) [CommRing R] {P Q : CochainComplex (ModuleCat R) ℤ} (f : P ⟶ Q) :
    (coneStandardShortComplex R f).ShortExact := coneStandardShortComplex_shortExact R f

#print axioms SerrePositivity.DerivedCompletion.complexTowerCompatibleLift_map
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitShortComplex_shortExact
#print axioms SerrePositivity.DerivedCompletion.coneStandardShortComplex_shortExact

-- G2-3: reconstruct complete objects through the actual standard unit.
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulProjection
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulInclusion_towerMap
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulProjection_towerMap
assert_no_sorry SerrePositivity.DerivedCompletion.complexPowerKoszulInclusion_projection_zero
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionTowerInclusion
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionReconstructionSequence
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionReconstructionSequence_shortExact
assert_no_sorry SerrePositivity.DerivedCompletion.constantComplexTowerUnit_comp_completionInclusion
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionReconstructionSequence_third_isZero
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionTowerInclusion_isIso_of_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionUnitObject_isIso_of_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionUnit_quasiIso_of_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.complexCompletionUnitIso
assert_no_sorry SerrePositivity.DerivedCompletion.derivedComplexCompletionUnit_isIso_of_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.derivedComplexCompletionUnitIso
assert_no_sorry SerrePositivity.DerivedCompletion.isComplete_iff_derivedComplexCompletionUnit_isIso

-- No boundedness, termwise completeness, or regularity assumptions enter reconstruction.
example (R : Type) [CommRing R] (a : R) (X : ConcreteDerivedCategory R) :
    IsComplete R a X ↔ IsIso ((derivedComplexCompletionUnit R a).app X) :=
  isComplete_iff_derivedComplexCompletionUnit_isIso R a X

example (R : Type) [CommRing R] (a : R) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    QuasiIso (complexCompletionUnit R a K) := complexCompletionUnit_quasiIso_of_isComplete R a K hK

-- The comparison is the standard unit already used in the projection diagrams.
example (R : Type) [CommRing R] (a : R) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    (complexCompletionUnitIso R a K hK).hom = complexCompletionUnitObject R a K := rfl

#print axioms SerrePositivity.DerivedCompletion.complexCompletionUnitObject_isIso_of_isComplete
#print axioms SerrePositivity.DerivedCompletion.isComplete_iff_derivedComplexCompletionUnit_isIso

-- G2-2b foundation: no finite projective dimension assumption.
assert_no_sorry SerrePositivity.cochainTensorMap_f_isIso_of_diagonal
assert_no_sorry SerrePositivity.cochainTensor_truncation_f_isIso
assert_no_sorry SerrePositivity.cochainTensor_acyclic_of_flat_boundedAbove
assert_no_sorry SerrePositivity.cochainTensor_quasiIso_left_of_boundedAboveFlat

#print axioms SerrePositivity.cochainTensor_acyclic_of_flat_boundedAbove
#print axioms SerrePositivity.cochainTensor_quasiIso_left_of_boundedAboveFlat

-- G2-2b: arbitrary bounded-above projective replacements and actual derived model comparisons.
assert_no_sorry SerrePositivity.cochainUnop
assert_no_sorry SerrePositivity.cochainUnopMap
assert_no_sorry SerrePositivity.cochainUnopMap_quasiIso
assert_no_sorry SerrePositivity.exists_boundedAbove_projective_resolution
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.isKProjective
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.ofBoundedAbove
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.comparison
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.comparisonHomotopy
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.comparison_quasiIso
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.comparisonHomotopyEquiv
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.comparisonHomotopyEquiv_hom
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.tensorModel
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.tensorAugmentation
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.tensorComparisonEquiv
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.tensorComparisonEquiv_hom
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.tensorComparisonAugmentationHomotopy
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.derivedTensorModel
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.derivedTensorComparisonIso
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.derivedTensorComparisonIso_augmentation

#print axioms SerrePositivity.exists_boundedAbove_projective_resolution
#print axioms SerrePositivity.BoundedAboveProjectiveResolution.derivedTensorComparisonIso_augmentation

-- G2-2b: coherent map laws and the natural augmentation in both variables.
assert_no_sorry SerrePositivity.homotopyOfDerivedMapEq
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.map
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.mapHomotopy
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.map_naturality
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.homotopyOfAugmentation
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.mapIdHomotopy
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.mapCompHomotopy
assert_no_sorry SerrePositivity.BoundedAboveProjectiveResolution.map_quasiIso
assert_no_sorry SerrePositivity.BoundedAboveCochain
assert_no_sorry SerrePositivity.boundedAboveChosenResolution
assert_no_sorry SerrePositivity.boundedAboveResolutionFunctor
assert_no_sorry SerrePositivity.cochainTensorMap_quasiIso_of_KProjective
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorFunctor
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorFunctor_map_isIso
assert_no_sorry SerrePositivity.boundedAboveOrdinaryTensorFunctor
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorAugmentation

#print axioms SerrePositivity.boundedAboveDerivedTensorFunctor
#print axioms SerrePositivity.boundedAboveDerivedTensorAugmentation

-- G2-2b: tensor on the actual bounded-above derived category.
assert_no_sorry SerrePositivity.exists_cochainMap_of_isKProjective
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.isKProjective
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.ofIsLE
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.map
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.map_Q
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.map_naturality
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.mapIdHomotopy
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.mapCompHomotopy
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.map_quasiIso
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.mapSquareHomotopy
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.ofResolution
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.ofResolutionMapHomotopy
assert_no_sorry SerrePositivity.boundedAboveDerivedChosenModel
assert_no_sorry SerrePositivity.boundedAboveDerivedQ
assert_no_sorry SerrePositivity.cochainTensor_isStrictlyLE
assert_no_sorry SerrePositivity.boundedAboveDerivedTensor
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorModelIso
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorComplexComparison

#print axioms SerrePositivity.boundedAboveDerivedTensor
#print axioms SerrePositivity.boundedAboveDerivedTensorComplexComparison

-- G2-2b: the actual derived associator is natural in all three variables.
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.mapHomotopyOfNaturality
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorModelIso_naturality
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorModel
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorLeftModelIso
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorRightModelIso
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorAssociator
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorLeftModelIso_naturality
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorRightModelIso_naturality
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorAssociator_naturality
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorAssociatorNatIso

#print axioms SerrePositivity.boundedAboveDerivedTensorAssociatorNatIso

-- G2-2b: both derived unitors are natural, with the standard R[0] as unit.
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorUnit
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorUnitSingleIso
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorUnitModel
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorLeftUnitor
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorRightUnitor
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorLeftUnitor_naturality
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorRightUnitor_naturality
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorLeftUnitorNatIso
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorRightUnitorNatIso

#print axioms SerrePositivity.boundedAboveDerivedTensorLeftUnitorNatIso
#print axioms SerrePositivity.boundedAboveDerivedTensorRightUnitorNatIso

-- G2-2b: derived scalar extension and tensor base change require no flatness.
assert_no_sorry SerrePositivity.mapCochain_quasiIso_of_KProjective
assert_no_sorry SerrePositivity.boundedAboveLeftDerived
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedModelIso
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedModelIso_naturality
assert_no_sorry SerrePositivity.cochainTensorMap_homogeneous
assert_no_sorry SerrePositivity.cochainTensorBaseChangeIso_naturality
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChange
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeModelIso
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeModel
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorBaseChangeIso
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorBaseChangeIso_naturality
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorBaseChangeNatIso

example (R : Type) [CommRing R] (I : Ideal R)
    (X Y : DerivedCategory.Minus (ModuleCat R)) :
    (SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        (SerrePositivity.boundedAboveDerivedTensor.obj (X, Y)) ≅
      SerrePositivity.boundedAboveDerivedTensor.obj
        ((SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj X,
          (SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj Y) :=
  SerrePositivity.boundedAboveDerivedTensorBaseChangeIso (Ideal.Quotient.mk I) X Y

#print axioms SerrePositivity.boundedAboveLeftDerived
#print axioms SerrePositivity.boundedAboveDerivedTensorBaseChangeNatIso
