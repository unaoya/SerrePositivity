module

public import SerrePositivity.Spectra.General.MappingObject
public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.CategoryTheory.Enriched.OfAdjunctionData

/-! # Composition and enrichment of general spectrum mapping objects

The C action represents mapping objects. Its coherence gives enriched composition
and units, compatible with the existing ordinary category of spectra.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

abbrev mappingObjectEvaluation (E F : GeneralSymmetricSpectrum C K) :
    pointwiseTensor (mappingObject E F) E ⟶ F :=
  RepresentedMappingEnrichment.evaluation pointwiseTensorBifunctor
    mappingObjectFunctor mappingObjectAdjunction E F

/-- C値写像対象の合成。後から適用する写像を左因子に置く。 -/
def mappingObjectComposition (E F G : GeneralSymmetricSpectrum C K) :
    mappingObject F G ⊗ mappingObject E F ⟶ mappingObject E G :=
  RepresentedMappingEnrichment.composition pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso mappingObjectFunctor
    mappingObjectAdjunction E F G

/-- 作用の単位比較を転置して得る写像対象の単位。 -/
def mappingObjectUnit (E : GeneralSymmetricSpectrum C K) :
    𝟙_ C ⟶ mappingObject E E :=
  RepresentedMappingEnrichment.unit pointwiseTensorBifunctor pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction E

/-- 通常のスペクトル射と写像対象の単位からの射の同値。 -/
def mappingObjectArrowEquiv (E F : GeneralSymmetricSpectrum C K) :
    (E ⟶ F) ≃ (𝟙_ C ⟶ mappingObject E F) :=
  RepresentedMappingEnrichment.arrowEquiv pointwiseTensorBifunctor
    pointwiseTensorUnitNatIso mappingObjectFunctor
    mappingObjectAdjunction E F

/-- 通常のスペクトル射を写像対象の点へ送る。 -/
def mappingObjectArrow {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F) :
    𝟙_ C ⟶ mappingObject E F :=
  RepresentedMappingEnrichment.arrow pointwiseTensorBifunctor pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction f


/-- 単位を左因子へ入れた合成の評価が通常の左単位からの評価に一致するという法則。 -/
def mappingObjectLeftUnitEvaluationLaw (E F : GeneralSymmetricSpectrum C K) : Prop :=
  RepresentedMappingEnrichment.leftUnitEvaluationLaw pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction E F

/-- 写像対象の左単位を合成した後の評価を計算する。 -/
lemma mappingObject_left_unit_evaluation (E F : GeneralSymmetricSpectrum C K) :
    mappingObjectLeftUnitEvaluationLaw E F := by
  apply RepresentedMappingEnrichment.left_unit_evaluation pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction E F
  · exact pointwiseTensorAssociator_parameter_left (mappingObjectUnit F)
      (mappingObject E F) E
  · exact RepresentedMappingEnrichment.unit_evaluation pointwiseTensorBifunctor
      pointwiseTensorUnitNatIso mappingObjectFunctor mappingObjectAdjunction F
  · exact pointwiseTensor_left_unit (mappingObject E F) E

/-- 単位を右因子へ入れた合成の評価が通常の右単位からの評価に一致するという法則。 -/
def mappingObjectRightUnitEvaluationLaw (E F : GeneralSymmetricSpectrum C K) : Prop :=
  RepresentedMappingEnrichment.rightUnitEvaluationLaw pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction E F

/-- 写像対象の右単位を合成した後の評価を計算する。 -/
lemma mappingObject_right_unit_evaluation (E F : GeneralSymmetricSpectrum C K) :
    mappingObjectRightUnitEvaluationLaw E F := by
  apply RepresentedMappingEnrichment.right_unit_evaluation pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction E F
  · exact pointwiseTensorAssociator_parameter_right (mappingObject E F)
      (mappingObjectUnit E) E
  · exact RepresentedMappingEnrichment.unit_evaluation pointwiseTensorBifunctor
      pointwiseTensorUnitNatIso mappingObjectFunctor mappingObjectAdjunction E
  · exact pointwiseTensor_triangle (mappingObject E F) E


/-- 三つの写像対象の反復合成を評価した射が等しいという法則。 -/
def mappingObjectAssociativityEvaluationLaw (E F G T : GeneralSymmetricSpectrum C K) : Prop :=
  RepresentedMappingEnrichment.associativityEvaluationLaw pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso mappingObjectFunctor
    mappingObjectAdjunction E F G T

/-- 反復合成の二つの経路は評価後に一致する。 -/
lemma mappingObject_associativity_evaluation (E F G T : GeneralSymmetricSpectrum C K) :
    mappingObjectAssociativityEvaluationLaw E F G T := by
  apply RepresentedMappingEnrichment.associativity_evaluation pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso mappingObjectFunctor
    mappingObjectAdjunction E F G T
  · exact pointwiseTensorAssociator_parameter_left (mappingObjectComposition F G T)
      (mappingObject E F) E
  · exact pointwiseTensorAssociator_parameter_right (mappingObject G T)
      (mappingObjectComposition E F G) E
  · exact SymmetricSequence.pointwiseAction_pentagon (SymmetricSequence.tensorPowerSequence K)
      pointwiseTensorAssociator pointwiseTensorPost pointwiseTensorAssociator_level
      pointwiseTensorPost_level (mappingObject G T) (mappingObject F G) (mappingObject E F) E


/-- 通常の二つの射に対応する点の合成の評価の法則。 -/
def mappingObjectArrowCompositionEvaluationLaw {E F G : GeneralSymmetricSpectrum C K}
    (f : E ⟶ F) (g : F ⟶ G) : Prop :=
  MappingArrowComposition.arrowCompositionEvaluationLaw pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    f g (mappingObjectArrow g) (mappingObjectArrow f)
    (mappingObjectEvaluation E F) (mappingObjectEvaluation F G)

/-- 点の合成の評価は、通常の二つの射の合成になる。 -/
lemma mappingObjectArrow_composition_evaluation {E F G : GeneralSymmetricSpectrum C K}
    (f : E ⟶ F) (g : F ⟶ G) : mappingObjectArrowCompositionEvaluationLaw f g := by
  apply MappingArrowComposition.arrow_composition_evaluation pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    f g (mappingObjectArrow g) (mappingObjectArrow f)
    (mappingObjectEvaluation E F) (mappingObjectEvaluation F G)
  · exact AdjunctionHomLaws.comparison_evaluation (mappingObjectAdjunction E)
      (pointwiseTensorUnitIso E) f
  · exact AdjunctionHomLaws.comparison_evaluation (mappingObjectAdjunction F)
      (pointwiseTensorUnitIso F) g
  · exact pointwiseTensorAssociator_parameter_naturality (mappingObjectArrow g)
      (mappingObjectArrow f) E
  · exact pointwiseTensor_triangle (𝟙_ C) E

/-- C-valued enrichment, with the ordinary order of composition factors. -/
@[instance_reducible]
def mappingEnrichedCategory : EnrichedCategory C (GeneralSymmetricSpectrum C K) :=
  RepresentedMappingEnrichment.enrichedCategory pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction
    (fun E F ↦ RepresentedMappingEnrichment.left_unit pointwiseTensorBifunctor
      pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso mappingObjectFunctor
      mappingObjectAdjunction E F (mappingObject_left_unit_evaluation E F))
    (fun E F ↦ RepresentedMappingEnrichment.right_unit pointwiseTensorBifunctor
      pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso mappingObjectFunctor
      mappingObjectAdjunction E F (mappingObject_right_unit_evaluation E F))
    (fun E F G T ↦ RepresentedMappingEnrichment.associativity pointwiseTensorBifunctor
      pointwiseTensorAssociatorNatIso mappingObjectFunctor mappingObjectAdjunction E F G T
      (mappingObject_associativity_evaluation E F G T))

/-- Enrichment compatible with the existing category of Sym(K) modules. -/
@[instance_reducible]
def mappingEnrichedOrdinaryCategory :
    EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  RepresentedMappingEnrichment.ordinaryCategory pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction
    (fun E F ↦ RepresentedMappingEnrichment.left_unit pointwiseTensorBifunctor
      pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso mappingObjectFunctor
      mappingObjectAdjunction E F (mappingObject_left_unit_evaluation E F))
    (fun E F ↦ RepresentedMappingEnrichment.right_unit pointwiseTensorBifunctor
      pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso mappingObjectFunctor
      mappingObjectAdjunction E F (mappingObject_right_unit_evaluation E F))
    (fun E F G T ↦ RepresentedMappingEnrichment.associativity pointwiseTensorBifunctor
      pointwiseTensorAssociatorNatIso mappingObjectFunctor mappingObjectAdjunction E F G T
      (mappingObject_associativity_evaluation E F G T))
    (RepresentedMappingEnrichment.arrow_identity pointwiseTensorBifunctor
      pointwiseTensorUnitNatIso mappingObjectFunctor mappingObjectAdjunction)
    (fun {E F G} f g ↦
      MappingArrowComposition.represented_arrow_composition pointwiseTensorBifunctor
        pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso (mappingObjectAdjunction E)
        f g (mappingObjectArrow g) (mappingObjectArrow f)
        (mappingObjectEvaluation E F) (mappingObjectEvaluation F G)
        (mappingObjectArrow_composition_evaluation f g))

end SerrePositivity.GeneralSymmetricSpectrum
