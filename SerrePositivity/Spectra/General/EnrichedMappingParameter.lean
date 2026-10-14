module

public import SerrePositivity.Spectra.General.EnrichedMappingObjects
public import SerrePositivity.Spectra.General.TensorMappingParameter
public import SerrePositivity.Spectra.General.CotensorMappingParameter

/-! # Parameter variance of the enriched Hom-object comparisons -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

local instance : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

lemma tensorEnrichedMappingIso_hom_app (X : C) (E F : GeneralSymmetricSpectrum C K) :
    ((tensorEnrichedMappingIso X).hom.app (op E)).app F = (tensorMappingIso X E F).hom := by
  change 𝟙 _ ≫ (tensorMappingIso X E F).hom ≫ (ihom X).map (𝟙 (mappingObject E F)) = _
  rw [Category.id_comp, (ihom X).map_id (mappingObject E F), Category.comp_id]

lemma cotensorEnrichedMappingIso_hom_app (X : C) (E F : GeneralSymmetricSpectrum C K) :
    ((cotensorEnrichedMappingIso X).hom.app (op E)).app F = (cotensorMappingIso X E F).hom := by
  change 𝟙 _ ≫ (cotensorMappingIso X E F).hom ≫ (ihom X).map (𝟙 (mappingObject E F)) = _
  rw [Category.id_comp, (ihom X).map_id (mappingObject E F), Category.comp_id]

/-- Parameter law required by tensor enriched representability. -/
lemma tensorEnrichedMappingIso_parameter {X Y : C} (f : X ⟶ Y)
    (E F : GeneralSymmetricSpectrum C K) :
    eHomWhiskerRight C ((pointwiseTensorBifunctor.map f).app E) F ≫
        ((tensorEnrichedMappingIso X).hom.app (op E)).app F =
      ((tensorEnrichedMappingIso Y).hom.app (op E)).app F ≫
        (MonoidalClosed.pre f).app (E ⟶[C] F) := by
  rw [tensorEnrichedMappingIso_hom_app, tensorEnrichedMappingIso_hom_app,
    eHomWhiskerRight_eq_mappingObjectMap]
  exact tensorMappingIso_naturality_parameter f E F

/-- Parameter law required by cotensor enriched representability. -/
lemma cotensorEnrichedMappingIso_parameter {X Y : C} (f : X ⟶ Y)
    (E F : GeneralSymmetricSpectrum C K) :
    eHomWhiskerLeft C E ((cotensorBifunctor.map f.op).app F) ≫
        ((cotensorEnrichedMappingIso X).hom.app (op E)).app F =
      ((cotensorEnrichedMappingIso Y).hom.app (op E)).app F ≫
        (MonoidalClosed.pre f).app (E ⟶[C] F) := by
  rw [cotensorEnrichedMappingIso_hom_app, cotensorEnrichedMappingIso_hom_app,
    eHomWhiskerLeft_eq_mappingObjectMap]
  exact cotensorMappingIso_naturality_parameter f E F

end SerrePositivity.GeneralSymmetricSpectrum
