module

public import SerrePositivity.Spectra.General.TensorMappingPoints

/-! # Ordinary points of the cotensor Hom-object comparison -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

lemma cotensorMappingPowerAdjunction_unit (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E ⟶ F) :
    (cotensorMappingPowerAdjunction X E).homEquiv (𝟙_ C) F
        (pointwiseTensorPost (ρ_ X).hom E ≫ f) =
      MonoidalClosed.curry' (mappingObjectHomEquiv X E F f) := by
  unfold cotensorMappingPowerAdjunction
  rw [Adjunction.comp_homEquiv]
  change (ihom.adjunction X).homEquiv (𝟙_ C) (mappingObject E F)
    (mappingObjectHomEquiv (X ⊗ (𝟙_ C)) E F (pointwiseTensorPost (ρ_ X).hom E ≫ f)) = _
  rw [mappingObjectHomEquiv_naturality_parameter]
  rfl

/-- The cotensor comparison preserves the ordinary point of a map into a cotensor. -/
lemma cotensorMappingIso_arrow (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : E ⟶ cotensor X F) :
    mappingObjectArrow f ≫ (cotensorMappingIso X E F).hom =
      MonoidalClosed.curry' (cotensorMappingHomEquiv X E F f) := by
  let g := (pointwiseTensorHomEquiv X E F).symm f
  have h := cotensorMappingNatIso_homEquiv X (𝟙_ C) E F
    (pointwiseTensorPost (ρ_ X).hom E ≫ g)
  have hu : (pointwiseTensorAssociator X (𝟙_ C) E).inv ≫
      pointwiseTensorPost (ρ_ X).hom E =
        (pointwiseTensorFunctor X).map (pointwiseTensorUnitIso E).hom := by
    have ht := pointwiseTensor_triangle X E
    change (pointwiseTensorAssociator X (𝟙_ C) E).hom ≫
      (pointwiseTensorFunctor X).map (pointwiseTensorUnitIso E).hom =
        pointwiseTensorPost (ρ_ X).hom E at ht
    rw [← ht, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hu, cotensorMappingPowerAdjunction_unit] at h
  have hp : (cotensorMappingAdjunction X E).homEquiv (𝟙_ C) F
      ((pointwiseTensorFunctor X).map (pointwiseTensorUnitIso E).hom ≫ g) =
        mappingObjectArrow f := by
    unfold cotensorMappingAdjunction
    rw [Adjunction.comp_homEquiv]
    change mappingObjectHomEquiv (𝟙_ C) E (cotensor X F)
      (pointwiseTensorHomEquiv X (pointwiseTensor (𝟙_ C) E) F
        ((pointwiseTensorFunctor X).map (pointwiseTensorUnitIso E).hom ≫ g)) = _
    rw [pointwiseTensorHomEquiv_naturality_source]
    have hg : pointwiseTensorHomEquiv X E F g = f :=
      (pointwiseTensorHomEquiv X E F).apply_symm_apply f
    rw [hg]
    exact (AdjunctionHomLaws.comparisonHomEquiv_apply
      (mappingObjectAdjunction E) (pointwiseTensorUnitIso E) f).symm
  rw [hp] at h
  exact h

local instance : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

/-- Ordinary-point compatibility required by enriched cotensor representability. -/
lemma cotensorEnrichedMappingIso_points (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : E ⟶ cotensor X F) :
    (MonoidalClosed.curryHomEquiv' (X := X) (Y := E ⟶[C] F)).symm
        (eHomEquiv C f ≫ ((cotensorEnrichedMappingIso X).hom.app (op E)).app F) =
      spectrumTensorCotensor.cotensorHomEquiv X E F f := by
  rw [cotensorEnrichedMappingIso_hom_app]
  change (MonoidalClosed.curryHomEquiv' (X := X) (Y := mappingObject E F)).symm
    (mappingObjectArrow f ≫ (cotensorMappingIso X E F).hom) = _
  rw [cotensorMappingIso_arrow]
  have hc := (MonoidalClosed.curryHomEquiv' (X := X) (Y := mappingObject E F)).symm_apply_apply
    (cotensorMappingHomEquiv X E F f)
  change MonoidalClosed.uncurry' (MonoidalClosed.curry' (cotensorMappingHomEquiv X E F f)) =
    cotensorMappingHomEquiv X E F f at hc
  change MonoidalClosed.uncurry' (MonoidalClosed.curry' (cotensorMappingHomEquiv X E F f)) = _
  rw [hc]
  change mappingObjectHomEquiv X E F ((pointwiseTensorHomEquiv X E F).symm f) = _
  rw [← spectrumTensorCotensor_tensorHomEquiv]
  rfl

end SerrePositivity.GeneralSymmetricSpectrum
