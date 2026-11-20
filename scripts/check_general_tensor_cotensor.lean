import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] (K : C)

-- All tests apply without a model structure or simplicial enrichment.
example (X : C) (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    level (pointwiseTensor X E) n = X ⊗ level E n := pointwiseTensor_level X E n

example (X : C) (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    level (cotensor X E) n = (ihom X).obj (level E n) := cotensor_level X E n

example (X : C) : pointwiseTensorFunctor (K := K) X ⊣ cotensorFunctor X :=
  pointwiseTensorCotensorAdjunction X

example (X : C) (E F : GeneralSymmetricSpectrum C K) (f : pointwiseTensor X E ⟶ F) :
    (pointwiseTensorHomEquiv X E F).symm (pointwiseTensorHomEquiv X E F f) = f :=
  (pointwiseTensorHomEquiv X E F).symm_apply_apply f

example (X : C) (E F : GeneralSymmetricSpectrum C K) (f : pointwiseTensor X E ⟶ F) :
    cotensorMappingHomEquiv X E F (pointwiseTensorHomEquiv X E F f) =
      mappingObjectHomEquiv X E F f := mappingHom_compatibility X E F f

example (E F : GeneralSymmetricSpectrum C K) :
    (E ⟶ F) ≃ (𝟙_ C ⟶ mappingObject E F) := ordinaryHomEquiv E F

example : pointwiseTensorFunctor (K := K) (𝟙_ C) ≅
    𝟭 (GeneralSymmetricSpectrum C K) := pointwiseTensorUnitNatIso

example (X Y : C) (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    (pointwiseTensorAssociator X Y E).hom.hom.app (FiniteBijection.of n) =
      (α_ X Y (level E n)).hom := pointwiseTensorAssociator_level X Y E n

example (X Y : C) : pointwiseTensorFunctor (K := K) (X ⊗ Y) ≅
    pointwiseTensorFunctor Y ⋙ pointwiseTensorFunctor X := pointwiseTensorAssociatorNatIso X Y

example (X : C) (E : GeneralSymmetricSpectrum C K) :
    (pointwiseTensorFunctor X).map ((pointwiseTensorCotensorAdjunction X).unit.app E) ≫
      (pointwiseTensorCotensorAdjunction X).counit.app ((pointwiseTensorFunctor X).obj E) =
        𝟙 _ := (pointwiseTensorCotensorAdjunction X).left_triangle_components E

example {X Y : C} (f : X ⟶ Y) (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    (pointwiseTensorPost f E).hom.app (FiniteBijection.of n) = f ▷ level E n :=
  pointwiseTensorPost_level f E n

example (X Y Z : C) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorPentagonLaw X Y Z E :=
  SymmetricSequence.pointwiseAction_pentagon (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorPost pointwiseTensorAssociator_level
    pointwiseTensorPost_level X Y Z E

example (X : C) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorTriangleLaw X E := pointwiseTensor_triangle X E

example (X : C) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorLeftUnitLaw X E := pointwiseTensor_left_unit X E

example : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

example (E F : GeneralSymmetricSpectrum C K) :
    mappingObjectArrowEquiv E F = ordinaryHomEquiv E F :=
  rfl

example (E : GeneralSymmetricSpectrum C K) :
    (mappingEnrichedCategory (K := K)).id E = mappingObjectUnit E :=
  rfl

example (E F G : GeneralSymmetricSpectrum C K) :
    (mappingEnrichedCategory (K := K)).comp E F G =
      ReverseComposition.reverse (mappingObjectComposition E F G) :=
  rfl

section
local instance : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

example (E F : GeneralSymmetricSpectrum C K) :
    (E ⟶[C] F) = mappingObject E F := rfl

example (E : GeneralSymmetricSpectrum C K) :
    (EnrichedOrdinaryCategory.homEquiv (V := C) (𝟙 E)) = mappingObjectUnit E := by
  exact RepresentedMappingEnrichment.arrow_identity pointwiseTensorBifunctor
    pointwiseTensorUnitNatIso mappingObjectFunctor mappingObjectAdjunction E

example (E : GeneralSymmetricSpectrum C K) {F G : GeneralSymmetricSpectrum C K} (g : F ⟶ G) :
    eHomWhiskerLeft C E g = (mappingObjectFunctor E).map g :=
  eHomWhiskerLeft_eq_mappingObjectMap E g

example {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F) (G : GeneralSymmetricSpectrum C K) :
    eHomWhiskerRight C f G = (mappingObjectBifunctor.map f.op).app G :=
  eHomWhiskerRight_eq_mappingObjectMap f G

example : eHomFunctor C (GeneralSymmetricSpectrum C K) ≅ mappingObjectBifunctor :=
  mappingEnrichedHomFunctorIso

example : SerrePositivity.Enriched.TensorCotensor C (GeneralSymmetricSpectrum C K) :=
  spectrumTensorCotensor

example (X : C) (E F : GeneralSymmetricSpectrum C K) (f : pointwiseTensor X E ⟶ F) :
    spectrumTensorCotensor.tensorHomEquiv X E F f = mappingObjectHomEquiv X E F f :=
  spectrumTensorCotensor_tensorHomEquiv X E F f

example (X : C) :
    SerrePositivity.Enriched.tensorEnrichedHom (spectrumTensorCotensor (K := K)) X ≅
      SerrePositivity.Enriched.powerHom (C := GeneralSymmetricSpectrum C K) X :=
  tensorEnrichedMappingIso X

example (X : C) :
    SerrePositivity.Enriched.cotensorEnrichedHom (spectrumTensorCotensor (K := K)) X ≅
      SerrePositivity.Enriched.powerHom (C := GeneralSymmetricSpectrum C K) X :=
  cotensorEnrichedMappingIso X

example {X Y : C} (f : X ⟶ Y) (E F : GeneralSymmetricSpectrum C K) :
    eHomWhiskerRight C ((pointwiseTensorBifunctor.map f).app E) F ≫
        ((tensorEnrichedMappingIso X).hom.app (Opposite.op E)).app F =
      ((tensorEnrichedMappingIso Y).hom.app (Opposite.op E)).app F ≫
        (MonoidalClosed.pre f).app (E ⟶[C] F) :=
  tensorEnrichedMappingIso_parameter f E F

example {X Y : C} (f : X ⟶ Y) (E F : GeneralSymmetricSpectrum C K) :
    eHomWhiskerLeft C E ((cotensorBifunctor.map f.op).app F) ≫
        ((cotensorEnrichedMappingIso X).hom.app (Opposite.op E)).app F =
      ((cotensorEnrichedMappingIso Y).hom.app (Opposite.op E)).app F ≫
        (MonoidalClosed.pre f).app (E ⟶[C] F) :=
  cotensorEnrichedMappingIso_parameter f E F

example : SerrePositivity.Enriched.EnrichedRepresentability
    (spectrumTensorCotensor (K := K)) := spectrumEnrichedRepresentability

example (X : C) (E F : GeneralSymmetricSpectrum C K) (f : pointwiseTensor X E ⟶ F) :
    (MonoidalClosed.curryHomEquiv' (X := X) (Y := E ⟶[C] F)).symm
        (eHomEquiv C f ≫ ((tensorEnrichedMappingIso X).hom.app (Opposite.op E)).app F) =
      spectrumTensorCotensor.tensorHomEquiv X E F f :=
  tensorEnrichedMappingIso_points X E F f

example (X : C) (E F : GeneralSymmetricSpectrum C K) (f : E ⟶ cotensor X F) :
    (MonoidalClosed.curryHomEquiv' (X := X) (Y := E ⟶[C] F)).symm
        (eHomEquiv C f ≫ ((cotensorEnrichedMappingIso X).hom.app (Opposite.op E)).app F) =
      spectrumTensorCotensor.cotensorHomEquiv X E F f :=
  cotensorEnrichedMappingIso_points X E F f

example (X : C) (E F : GeneralSymmetricSpectrum C K) (f : pointwiseTensor X E ⟶ F) :
    eHomEquiv C f ≫ (spectrumEnrichedRepresentability.homObjectComparison X E F).hom =
      eHomEquiv C (pointwiseTensorHomEquiv X E F f) :=
  spectrumEnrichedRepresentability.homObjectComparison_points X E F f

section ModelCompatibility
variable [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory (GeneralSymmetricSpectrum C K)]
example : SerrePositivity.Quillen.IsQuillenBifunctor (pointwiseTensorBifunctor (K := K)) ↔
    SerrePositivity.Quillen.HasQuillenPullbackHom
      (eHomFunctor C (GeneralSymmetricSpectrum C K)) :=
  SerrePositivity.Enriched.tensor_iff_mapping_model spectrumTensorCotensor
end ModelCompatibility
end

example : pointwiseTensorBifunctor (K := K) ⊣₂ cotensorBifunctor :=
  pointwiseTensorCotensorParametrizedAdjunction

example {X Y : C} (f : X ⟶ Y) (E F : GeneralSymmetricSpectrum C K)
    (g : pointwiseTensor Y E ⟶ F) :
    pointwiseTensorHomEquiv X E F ((pointwiseTensorBifunctor.map f).app E ≫ g) =
      pointwiseTensorHomEquiv Y E F g ≫ (cotensorBifunctor.map f.op).app F :=
  pointwiseTensorHomEquiv_naturality_parameter f E F g

example : (pointwiseTensorBifunctor (K := K)).flip ⊣₂ mappingObjectBifunctor :=
  pointwiseTensorMappingParametrizedAdjunction

example (X : C) {E E' : GeneralSymmetricSpectrum C K} (a : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor X E' ⟶ F) :
    mappingObjectHomEquiv X E F ((pointwiseTensorFunctor X).map a ≫ g) =
      mappingObjectHomEquiv X E' F g ≫ (mappingObjectBifunctor.map a.op).app F :=
  mappingObjectHomEquiv_naturality_source X a F g

example (X : C) (E F : GeneralSymmetricSpectrum C K) :
    mappingObject (pointwiseTensor X E) F ≅ (ihom X).obj (mappingObject E F) :=
  tensorMappingIso X E F

example (X : C) (E F : GeneralSymmetricSpectrum C K) :
    mappingObject E (cotensor X F) ≅ (ihom X).obj (mappingObject E F) :=
  cotensorMappingIso X E F

example (X Z : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor (Z ⊗ X) E ⟶ F) :
    mappingObjectHomEquiv Z (pointwiseTensor X E) F
        ((pointwiseTensorAssociator Z X E).inv ≫ f) ≫ (tensorMappingIso X E F).hom =
      (tensorMappingPowerAdjunction X E).homEquiv Z F f :=
  tensorMappingNatIso_homEquiv X Z E F f

example (X Z : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor (X ⊗ Z) E ⟶ F) :
    (cotensorMappingAdjunction X E).homEquiv Z F
        ((pointwiseTensorAssociator X Z E).inv ≫ f) ≫ (cotensorMappingIso X E F).hom =
      (cotensorMappingPowerAdjunction X E).homEquiv Z F f :=
  cotensorMappingNatIso_homEquiv X Z E F f

example (X : C) {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) :
    (mappingObjectBifunctor.map ((pointwiseTensorFunctor X).map f).op).app F ≫
        (tensorMappingIso X E F).hom =
      (tensorMappingIso X E' F).hom ≫ (ihom X).map ((mappingObjectBifunctor.map f.op).app F) :=
  tensorMappingIso_naturality_source X f F

example (X : C) {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) :
    (mappingObjectBifunctor.map f.op).app ((cotensorFunctor X).obj F) ≫
        (cotensorMappingIso X E F).hom =
      (cotensorMappingIso X E' F).hom ≫ (ihom X).map ((mappingObjectBifunctor.map f.op).app F) :=
  cotensorMappingIso_naturality_source X f F

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.Spectra.General).isPrefixOf mod ||
        mod == `SerrePositivity.CategoryTheory.ParametrizedAdjunctionTransport ||
        mod == `SerrePositivity.CategoryTheory.Monoidal.MappingWhiskering ||
        mod == `SerrePositivity.CategoryTheory.Monoidal.ActionComparisonAdjunction ||
        mod == `SerrePositivity.CategoryTheory.Monoidal.ActionComparisonNaturality do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No general spectrum declarations audited"
  logInfo m!"General tensor/cotensor and adjunction transport audit passed: {count} declarations, standard axioms only."
