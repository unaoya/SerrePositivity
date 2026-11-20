module

public import SerrePositivity.Spectra.General.MappingFunctorComparison
public import SerrePositivity.Spectra.SymmetricSpectrum.Basic
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
def legacyPointedHomFunctorIso :=
  GeneralSymmetricSpectrum.mappingEnrichedHomFunctorIso (K := PointedSimplicialSet.circle.{u})

local instance legacyOrdinaryCategory :
    EnrichedOrdinaryCategory SSet.{u} SymmetricSpectrum.{u} :=
  @TransportOrdinaryEnrichment.ordinaryCategory
    _ _ _ _ _ _ PointedSimplicialSet.forget.{u} _ SymmetricSpectrum.{u} _
    (GeneralSymmetricSpectrum.mappingEnrichedOrdinaryCategory (K := PointedSimplicialSet.circle.{u}))
    PointedSimplicialSet.forgetUnitHomEquiv.{u}
    PointedSimplicialSet.forgetUnitHomEquiv_formula.{u}

/-- The ordinary simplicial enriched Hom is the actual model mapping bifunctor. -/
def legacyOrdinaryHomFunctorIso :=
  let pointed := GeneralSymmetricSpectrum.mappingEnrichedOrdinaryCategory
    (K := PointedSimplicialSet.circle.{u})
  let transported := @TransportOrdinaryEnrichment.homFunctorIso
    _ _ _ _ _ _ PointedSimplicialSet.forget.{u} _ SymmetricSpectrum.{u} _ pointed
    PointedSimplicialSet.forgetUnitHomEquiv.{u}
    PointedSimplicialSet.forgetUnitHomEquiv_formula.{u}
  let whiskered := Functor.isoWhiskerRight legacyPointedHomFunctorIso
    ((Functor.whiskeringRight SymmetricSpectrum.{u} PointedSimplicialSet.{u} SSet.{u}).obj
      PointedSimplicialSet.forget.{u})
  transported.symm ≪≫ whiskered

/-- SM7 for the original chosen simplicial enrichment, including both map actions. -/
lemma legacyOrdinaryHom_SM7 [HomotopicalAlgebra.ModelCategory SSet.{u}]
    (hCof : HomotopicalAlgebra.cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
    (hFib : HomotopicalAlgebra.fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp) :
    let := simplicialLevelModelCategory hCof hFib
    Quillen.HasQuillenPullbackHom (eHomFunctor SSet.{u} SymmetricSpectrum.{u}) := by
  let := simplicialLevelModelCategory hCof hFib
  let : Quillen.IsQuillenBifunctor ordinarySpectrumTensor.{u} :=
    ordinarySpectrumTensor_isQuillen hCof hFib
  let comparison := ParametrizedAdjunctionTransport.right ordinarySpectrumMappingAdjunction
    legacyOrdinaryHomFunctorIso.symm
  exact (Quillen.isQuillenBifunctor_iff_pullbackHom comparison).1 inferInstance

end SerrePositivity.SimplicialModelInputs
