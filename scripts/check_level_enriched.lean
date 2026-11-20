import SerrePositivity.Spectra.ModelCategory.SimplicialLevelEnriched
import SerrePositivity.Spectra.ModelCategory.SimplicialHomComparison
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.Quillen SerrePositivity.SimplicialModelInputs

section General
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] (K : C)
  [ModelCategory C] [ModelCategory (GeneralSymmetricSpectrum C K)]
  [IsLeftQuillen (GeneralSymmetricSpectrum.freeAt (K := K) 0)]
  [IsQuillenBifunctor (curriedTensor (GeneralSymmetricSpectrum C K))]

example : IsQuillenBifunctor (GeneralSymmetricSpectrum.pointwiseTensorBifunctor (K := K)) :=
  GeneralSymmetricSpectrum.pointwiseTensor_isQuillen
example : HasQuillenPullbackHom (GeneralSymmetricSpectrum.cotensorBifunctor (K := K)) :=
  GeneralSymmetricSpectrum.cotensor_hasQuillenPullbackHom
example : HasQuillenPullbackHom (GeneralSymmetricSpectrum.mappingObjectBifunctor (K := K)) :=
  GeneralSymmetricSpectrum.mappingObject_hasQuillenPullbackHom
example : let : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
      GeneralSymmetricSpectrum.mappingEnrichedOrdinaryCategory
    HasQuillenPullbackHom (eHomFunctor C (GeneralSymmetricSpectrum C K)) :=
  GeneralSymmetricSpectrum.enrichedHom_hasQuillenPullbackHom
end General

section LegacyPointed
example :
    let : EnrichedOrdinaryCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
      GeneralSymmetricSpectrum.mappingEnrichedOrdinaryCategory (K := PointedSimplicialSet.circle.{u})
    eHomFunctor PointedSimplicialSet.{u} SymmetricSpectrum.{u} ≅ pointedSpectrumMapping.{u} :=
  legacyPointedHomFunctorIso
end LegacyPointed

section LegacyOrdinary
local instance : EnrichedOrdinaryCategory SSet.{u} SymmetricSpectrum.{u} :=
  by
    letI := SymmetricSpectrum.pointedMappingEnrichedOrdinaryCategory.{u}
    exact TransportOrdinaryEnrichment.ordinaryCategory PointedSimplicialSet.forget.{u}
      SymmetricSpectrum.{u} PointedSimplicialSet.forgetUnitHomEquiv.{u}
      PointedSimplicialSet.forgetUnitHomEquiv_formula.{u}
example : eHomFunctor SSet.{u} SymmetricSpectrum.{u} ≅ ordinarySpectrumMapping.{u} :=
  legacyOrdinaryHomFunctorIso
example [ModelCategory SSet.{u}]
    (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
    (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp) :
    let := simplicialLevelModelCategory hCof hFib
    HasQuillenPullbackHom (eHomFunctor SSet.{u} SymmetricSpectrum.{u}) :=
  legacyOrdinaryHom_SM7 hCof hFib
end LegacyOrdinary

section Concrete
variable [ModelCategory SSet.{u}]
  (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
  (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)

example : let := simplicialLevelModelCategory hCof hFib
    IsQuillenBifunctor pointedSpectrumTensor.{u} := pointedSpectrumTensor_isQuillen hCof hFib
example : let := simplicialLevelModelCategory hCof hFib
    HasQuillenPullbackHom pointedSpectrumCotensor.{u} := pointedSpectrumCotensor_SM7 hCof hFib
example : let := simplicialLevelModelCategory hCof hFib
    HasQuillenPullbackHom pointedSpectrumMapping.{u} := pointedSpectrumMapping_SM7 hCof hFib
example : let := simplicialLevelModelCategory hCof hFib
    IsQuillenBifunctor ordinarySpectrumTensor.{u} := ordinarySpectrumTensor_isQuillen hCof hFib
example : let := simplicialLevelModelCategory hCof hFib
    HasQuillenPullbackHom ordinarySpectrumCotensor.{u} := ordinarySpectrumCotensor_SM7 hCof hFib
example : let := simplicialLevelModelCategory hCof hFib
    HasQuillenPullbackHom ordinarySpectrumMapping.{u} := ordinarySpectrumMapping_SM7 hCof hFib
example (K : SSet.{u}) :
    ordinarySpectrumTensor.obj K = SymmetricSpectrum.simplicialTensorFunctor K :=
  ordinarySpectrumTensor_obj K
example (K : SSet.{u}) (E : SymmetricSpectrum.{u}) :
    (ordinarySpectrumCotensor.obj (Opposite.op K)).obj E = SymmetricSpectrum.simplicialCotensor K E :=
  ordinarySpectrumCotensor_obj K E
example (E F : SymmetricSpectrum.{u}) :
    (ordinarySpectrumMapping.obj (Opposite.op E)).obj F = SymmetricSpectrum.simplicialMappingSpace E F :=
  ordinarySpectrumMapping_obj E F
end Concrete

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless #[`SerrePositivity.HomotopicalAlgebra.Monoidal.BifunctorTransport,
        `SerrePositivity.Spectra.General.EnrichedModel,
        `SerrePositivity.Spectra.ModelCategory.SimplicialLevelEnriched,
        `SerrePositivity.Spectra.ModelCategory.SimplicialHomComparison].contains
        env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No enriched model declarations audited"
  logInfo m!"Spectrum enriched model audit passed: {count} declarations, standard axioms only."
