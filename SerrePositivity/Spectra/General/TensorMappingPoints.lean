module

public import SerrePositivity.Spectra.General.EnrichedMappingParameter

/-! # Ordinary points of the tensor Hom-object comparison -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

lemma tensorMappingPowerAdjunction_unit (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E ⟶ F) :
    (tensorMappingPowerAdjunction X E).homEquiv (𝟙_ C) F
        (pointwiseTensorPost (λ_ X).hom E ≫ f) =
      MonoidalClosed.curry' (mappingObjectHomEquiv X E F f) := by
  unfold tensorMappingPowerAdjunction
  rw [Adjunction.comp_homEquiv]
  change (((ihom.adjunction X).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight X)).homEquiv (𝟙_ C) (mappingObject E F))
      (mappingObjectHomEquiv ((𝟙_ C) ⊗ X) E F (pointwiseTensorPost (λ_ X).hom E ≫ f)) = _
  rw [mappingObjectHomEquiv_naturality_parameter, Adjunction.homEquiv_ofNatIsoLeft_apply]
  change MonoidalClosed.curry ((β_ X (𝟙_ C)).hom ≫ (λ_ X).hom ≫
    mappingObjectHomEquiv X E F f) =
      MonoidalClosed.curry ((ρ_ X).hom ≫ mappingObjectHomEquiv X E F f)
  rw [← Category.assoc, braiding_leftUnitor]

/-- The tensor comparison sends the ordinary point to the closed transpose
of the same parameter/mapping adjunction. -/
lemma tensorMappingIso_arrow (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E ⟶ F) :
    mappingObjectArrow f ≫ (tensorMappingIso X E F).hom =
      MonoidalClosed.curry' (mappingObjectHomEquiv X E F f) := by
  have h := tensorMappingNatIso_homEquiv X (𝟙_ C) E F
    (pointwiseTensorPost (λ_ X).hom E ≫ f)
  have hu : (pointwiseTensorAssociator (𝟙_ C) X E).inv ≫
      pointwiseTensorPost (λ_ X).hom E = (pointwiseTensorUnitIso (pointwiseTensor X E)).hom := by
    have hl := pointwiseTensor_left_unit X E
    change (pointwiseTensorAssociator (𝟙_ C) X E).hom ≫
      (pointwiseTensorUnitIso (pointwiseTensor X E)).hom = pointwiseTensorPost (λ_ X).hom E at hl
    rw [← hl, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hu, tensorMappingPowerAdjunction_unit] at h
  change mappingObjectHomEquiv (𝟙_ C) (pointwiseTensor X E) F
    ((pointwiseTensorUnitIso (pointwiseTensor X E)).hom ≫ f) ≫ _ = _ at h
  have hp := AdjunctionHomLaws.comparisonHomEquiv_apply
    (mappingObjectAdjunction (pointwiseTensor X E))
    (pointwiseTensorUnitIso (pointwiseTensor X E)) f
  change mappingObjectArrow f = mappingObjectHomEquiv (𝟙_ C) (pointwiseTensor X E) F
    ((pointwiseTensorUnitIso (pointwiseTensor X E)).hom ≫ f) at hp
  rw [← hp] at h
  exact h

local instance : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

/-- Ordinary-point compatibility required by enriched tensor representability. -/
lemma tensorEnrichedMappingIso_points (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E ⟶ F) :
    (MonoidalClosed.curryHomEquiv' (X := X) (Y := E ⟶[C] F)).symm
        (eHomEquiv C f ≫ ((tensorEnrichedMappingIso X).hom.app (op E)).app F) =
      spectrumTensorCotensor.tensorHomEquiv X E F f := by
  rw [tensorEnrichedMappingIso_hom_app, spectrumTensorCotensor_tensorHomEquiv]
  change (MonoidalClosed.curryHomEquiv' (X := X) (Y := mappingObject E F)).symm
    (mappingObjectArrow f ≫ (tensorMappingIso X E F).hom) = _
  rw [tensorMappingIso_arrow]
  exact (MonoidalClosed.curryHomEquiv' (X := X) (Y := mappingObject E F)).symm_apply_apply _

end SerrePositivity.GeneralSymmetricSpectrum
