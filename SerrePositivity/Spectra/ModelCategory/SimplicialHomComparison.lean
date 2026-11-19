module

public import SerrePositivity.CategoryTheory.Enriched.RepresentedMapping
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpacePointedOrdinary
public import SerrePositivity.Spectra.ModelCategory.SimplicialLevelEnriched

/-! # Comparing the existing spectrum enrichment with the mapping bifunctor -/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SerrePositivity.SimplicialModelInputs

local instance legacyPointedOrdinaryCategory :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
  SymmetricSpectrum.pointedMappingEnrichedOrdinaryCategory

/-- Comparison in both spectrum variables with the existing chosen enrichment. -/
def legacyPointedHomFunctorIso : eHomFunctor PointedSimplicialSet.{u} SymmetricSpectrum.{u} ≅
    SymmetricSpectrum.pointedMappingSpaceBifunctor.{u} :=
  RepresentedHomFunctor.homFunctorIso_ofParametrized
    (H := SymmetricSpectrum.pointwiseTensorBifunctor.{u})
    (a := SymmetricSpectrum.pointwiseTensorAssociatorNatIso.{u})
    (u := SymmetricSpectrum.pointwiseTensorUnitNatIso.{u})
    (hL := fun p Q E ↦ GeneralSymmetricSpectrum.pointwiseTensorAssociator_parameter_left p Q E)
    (hR := fun P {_ _} q E ↦ GeneralSymmetricSpectrum.pointwiseTensorAssociator_parameter_right P q E)
    (huL := GeneralSymmetricSpectrum.pointwiseTensorBifunctor_left_unit
      (K := PointedSimplicialSet.circle.{u}))
    (huR := GeneralSymmetricSpectrum.pointwiseTensorBifunctor_triangle
      (K := PointedSimplicialSet.circle.{u}))
    (B := SymmetricSpectrum.pointedMappingSpaceBifunctor.{u})
    SymmetricSpectrum.pointedMappingSpaceParametrizedAdjunction.{u}
    SymmetricSpectrum.mappingSpace_left_unit.{u}
    SymmetricSpectrum.mappingSpace_right_unit.{u}
    SymmetricSpectrum.mappingSpace_associativity.{u}
    SymmetricSpectrum.mappingSpaceArrow_identity.{u}
    (fun f g ↦ SymmetricSpectrum.mappingSpaceArrow_composition f g)

local instance legacyOrdinaryCategory :
    EnrichedOrdinaryCategory SSet.{u} SymmetricSpectrum.{u} :=
  SymmetricSpectrum.mappingSpaceSimplicialCategory

/-- The ordinary simplicial enriched Hom is the actual model mapping bifunctor. -/
def legacyOrdinaryHomFunctorIso : eHomFunctor SSet.{u} SymmetricSpectrum.{u} ≅
    ordinarySpectrumMapping.{u} :=
  (TransportOrdinaryEnrichment.homFunctorIso PointedSimplicialSet.forget.{u}
    SymmetricSpectrum.{u} PointedSimplicialSet.forgetUnitHomEquiv.{u}
    PointedSimplicialSet.forgetUnitHomEquiv_formula.{u}).symm ≪≫
  Functor.isoWhiskerRight legacyPointedHomFunctorIso
    ((Functor.whiskeringRight SymmetricSpectrum.{u} PointedSimplicialSet.{u} SSet.{u}).obj
      PointedSimplicialSet.forget.{u})

/-- SM7 for the original chosen simplicial enrichment, including both map actions. -/
lemma legacyOrdinaryHom_SM7 [HomotopicalAlgebra.ModelCategory SSet.{u}]
    (hCof : HomotopicalAlgebra.cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
    (hFib : HomotopicalAlgebra.fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp) :
    let := simplicialLevelModelCategory hCof hFib
    Quillen.HasQuillenPullbackHom (eHomFunctor SSet.{u} SymmetricSpectrum.{u}) := by
  let := simplicialLevelModelCategory hCof hFib
  let : Quillen.IsQuillenBifunctor ordinarySpectrumTensor.{u} :=
    ordinarySpectrumTensor_isQuillen hCof hFib
  exact (Quillen.isQuillenBifunctor_iff_pullbackHom
    (ParametrizedAdjunctionTransport.right ordinarySpectrumMappingAdjunction
      legacyOrdinaryHomFunctorIso.symm)).1 inferInstance

end SerrePositivity.SimplicialModelInputs
