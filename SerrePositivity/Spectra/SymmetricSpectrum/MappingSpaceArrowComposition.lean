module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceAssociativity
public import SerrePositivity.CategoryTheory.Enriched.RepresentedMapping

/-! # 通常のスペクトル射の合成と基点付き写像対象の合成の一致 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (pointwiseTensorUnitIso)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 通常の射を写像対象の点へ送った後の評価の法則。 -/
def mappingSpaceArrowEvaluationLaw {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) : Prop :=
  AdjunctionHomLaws.comparisonEvaluationLaw (pointedMappingSpaceAdjunction E)
    (pointwiseTensorUnitIso E) f

/-- 射に対応する点を評価すると、作用の単位比較と元の射の合成になる。 -/
lemma mappingSpaceArrow_evaluation {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    mappingSpaceArrowEvaluationLaw f :=
  AdjunctionHomLaws.comparison_evaluation (pointedMappingSpaceAdjunction E)
    (pointwiseTensorUnitIso E) f

/-- 通常の二つの射に対応する点の合成の評価の法則。 -/
def mappingSpaceArrowCompositionEvaluationLaw {E F G : SymmetricSpectrum.{u}}
    (f : E ⟶ F) (g : F ⟶ G) : Prop :=
  MappingArrowComposition.arrowCompositionEvaluationLaw pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    f g (mappingSpaceArrow g) (mappingSpaceArrow f)
    (mappingSpaceEvaluation E F) (mappingSpaceEvaluation F G)

/-- 点の合成の評価は、通常の二つの射の合成になる。 -/
lemma mappingSpaceArrow_composition_evaluation {E F G : SymmetricSpectrum.{u}}
    (f : E ⟶ F) (g : F ⟶ G) : mappingSpaceArrowCompositionEvaluationLaw f g := by
  apply MappingArrowComposition.arrow_composition_evaluation pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    f g (mappingSpaceArrow g) (mappingSpaceArrow f)
    (mappingSpaceEvaluation E F) (mappingSpaceEvaluation F G)
  · exact mappingSpaceArrow_evaluation f
  · exact mappingSpaceArrow_evaluation g
  · exact GeneralSymmetricSpectrum.pointwiseTensorAssociator_parameter_naturality (mappingSpaceArrow g)
      (mappingSpaceArrow f) E
  · exact GeneralSymmetricSpectrum.pointwiseTensor_triangle (𝟙_ PointedSimplicialSet.{u}) E

/-- 通常の射の合成と写像対象の点の合成が一致するという法則。 -/
def mappingSpaceArrowCompositionLaw {E F G : SymmetricSpectrum.{u}}
    (f : E ⟶ F) (g : F ⟶ G) : Prop :=
  RepresentedMappingEnrichment.arrowCompositionLaw pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u} f g

/-- 通常の射の合成は写像対象の点の合成に対応する。 -/
lemma mappingSpaceArrow_composition {E F G : SymmetricSpectrum.{u}}
    (f : E ⟶ F) (g : F ⟶ G) : mappingSpaceArrowCompositionLaw f g :=
  MappingArrowComposition.represented_arrow_composition pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    (pointedMappingSpaceAdjunction E) f g (mappingSpaceArrow g) (mappingSpaceArrow f)
    (mappingSpaceEvaluation E F) (mappingSpaceEvaluation F G)
    (mappingSpaceArrow_composition_evaluation f g)

end SerrePositivity.SymmetricSpectrum
