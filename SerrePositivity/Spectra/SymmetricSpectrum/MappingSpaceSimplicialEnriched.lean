module

public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceEnriched
public import SerrePositivity.CategoryTheory.Enriched.Transport

/-! # 基点を忘れた単体的写像対象の合成の整合性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 基点付きの豊穣構造を忘却関手の比較で移した単体的豊穣圏。 -/
@[instance_reducible]
def simplicialMappingEnrichedCategory : EnrichedCategory SSet.{u} SymmetricSpectrum.{u} := by
  let : EnrichedCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
    pointedMappingEnrichedCategory
  exact TransportEnrichmentComparisons.category PointedSimplicialSet.forget.{u}
    SymmetricSpectrum.{u}

/-- 移した豊穣圏の写像対象は、基点を忘れた写像対象。 -/
lemma simplicialMappingEnrichedCategory_hom (E F : SymmetricSpectrum.{u}) :
    simplicialMappingEnrichedCategory.Hom E F = simplicialMappingSpace E F := rfl

/-- 移した豊穣圏の合成と構成済みの直積からの合成の一致の法則。 -/
def simplicialMappingEnrichedCompositionLaw (E F G : SymmetricSpectrum.{u}) : Prop :=
  let : EnrichedCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
    pointedMappingEnrichedCategory
  TransportEnrichmentComparisons.reverseCompositionLaw PointedSimplicialSet.forget.{u}
    SymmetricSpectrum.{u} E F G (mappingSpaceComposition E F G)

/-- 移した豊穣圏の合成は構成済みの直積からの合成に一致する。 -/
lemma simplicialMappingEnrichedCategory_comp (E F G : SymmetricSpectrum.{u}) :
    simplicialMappingEnrichedCompositionLaw E F G := by
  let : EnrichedCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
    pointedMappingEnrichedCategory
  exact TransportEnrichmentComparisons.reverse_composition PointedSimplicialSet.forget.{u}
    SymmetricSpectrum.{u} E F G (mappingSpaceComposition E F G)
    (pointedMappingEnrichedCategory_comp E F G)

/-- 移した豊穣圏の単位と構成済みの通常の単体写像の単位の一致の法則。 -/
def simplicialMappingEnrichedIdentityLaw (E : SymmetricSpectrum.{u}) : Prop :=
  let : EnrichedCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
    pointedMappingEnrichedCategory
  TransportEnrichmentComparisons.identityLaw PointedSimplicialSet.forget.{u}
    SymmetricSpectrum.{u} E (simplicialMappingUnit E)

/-- 移した豊穣圏の単位は構成済みの非基点側の単位に一致する。 -/
lemma simplicialMappingEnrichedCategory_id (E : SymmetricSpectrum.{u}) :
    simplicialMappingEnrichedIdentityLaw E := by
  let : EnrichedCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
    pointedMappingEnrichedCategory
  exact TransportEnrichmentComparisons.identity_eq PointedSimplicialSet.forget.{u}
    SymmetricSpectrum.{u} E (mappingSpaceUnit E) (pointedMappingEnrichedCategory_id E)
    (simplicialMappingUnit E)
    (PointedSimplicialSet.forgetUnit_comp (pointedMappingSpace E E) (mappingSpaceUnit E))

end SerrePositivity.SymmetricSpectrum
