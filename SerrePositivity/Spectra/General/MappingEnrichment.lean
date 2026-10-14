module

public import SerrePositivity.Spectra.General.MappingObject
public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.CategoryTheory.Monoidal.RepresentedMappingEnrichment

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

/-- 二つの写像対象をテンソルした作用から、評価を二回適用する射。 -/
def mappingObjectCompositionEvaluation (E F G : GeneralSymmetricSpectrum C K) :
    pointwiseTensor (mappingObject F G ⊗ mappingObject E F) E ⟶ G :=
  RepresentedMappingEnrichment.compositionEvaluation pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso mappingObjectFunctor
    mappingObjectAdjunction E F G

/-- C値写像対象の合成。後から適用する写像を左因子に置く。 -/
def mappingObjectComposition (E F G : GeneralSymmetricSpectrum C K) :
    mappingObject F G ⊗ mappingObject E F ⟶ mappingObject E G :=
  RepresentedMappingEnrichment.composition pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso mappingObjectFunctor
    mappingObjectAdjunction E F G

/-- 合成を作用へ送って評価すると二回の評価に一致するという法則。 -/
def mappingObjectCompositionEvaluationLaw (E F G : GeneralSymmetricSpectrum C K) : Prop :=
  RepresentedMappingEnrichment.compositionEvaluationLaw pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso mappingObjectFunctor
    mappingObjectAdjunction E F G

/-- 写像対象の合成は二回の評価を表現する。 -/
lemma mappingObjectComposition_evaluation (E F G : GeneralSymmetricSpectrum C K) :
    mappingObjectCompositionEvaluationLaw E F G :=
  RepresentedMappingEnrichment.composition_evaluation pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso mappingObjectFunctor
    mappingObjectAdjunction E F G

/-- 作用の単位比較を転置して得る写像対象の単位。 -/
def mappingObjectUnit (E : GeneralSymmetricSpectrum C K) :
    𝟙_ C ⟶ mappingObject E E :=
  RepresentedMappingEnrichment.unit pointwiseTensorBifunctor pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction E

/-- 写像対象の単位を作用へ送って評価すると作用の単位比較になるという法則。 -/
def mappingObjectUnitEvaluationLaw (E : GeneralSymmetricSpectrum C K) : Prop :=
  RepresentedMappingEnrichment.unitEvaluationLaw pointwiseTensorBifunctor
    pointwiseTensorUnitNatIso mappingObjectFunctor
    mappingObjectAdjunction E

/-- 写像対象の単位は作用の単位比較を表現する。 -/
lemma mappingObjectUnit_evaluation (E : GeneralSymmetricSpectrum C K) :
    mappingObjectUnitEvaluationLaw E :=
  RepresentedMappingEnrichment.unit_evaluation pointwiseTensorBifunctor
    pointwiseTensorUnitNatIso mappingObjectFunctor
    mappingObjectAdjunction E

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

/-- 写像対象の点から通常のスペクトル射を得る。 -/
def mappingObjectArrowInverse {E F : GeneralSymmetricSpectrum C K}
    (f : 𝟙_ C ⟶ mappingObject E F) : E ⟶ F :=
  (mappingObjectArrowEquiv E F).symm f

/-- 恒等射の対応先は作用の単位比較の転置という法則。 -/
def mappingObjectArrowIdentityLaw (E : GeneralSymmetricSpectrum C K) : Prop :=
  RepresentedMappingEnrichment.arrowIdentityLaw pointwiseTensorBifunctor
    pointwiseTensorUnitNatIso mappingObjectFunctor
    mappingObjectAdjunction E

/-- 恒等射は写像対象の単位に対応する。 -/
lemma mappingObjectArrow_identity (E : GeneralSymmetricSpectrum C K) :
    mappingObjectArrowIdentityLaw E :=
  RepresentedMappingEnrichment.arrow_identity pointwiseTensorBifunctor
    pointwiseTensorUnitNatIso mappingObjectFunctor
    mappingObjectAdjunction E


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
  · exact mappingObjectUnit_evaluation F
  · exact pointwiseTensor_left_unit (mappingObject E F) E

/-- 写像対象の左単位則の等式。 -/
def mappingObjectLeftUnitLaw (E F : GeneralSymmetricSpectrum C K) : Prop :=
  RepresentedMappingEnrichment.leftUnitLaw pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction E F

/-- C値写像対象の合成は左単位則を満たす。 -/
lemma mappingObject_left_unit (E F : GeneralSymmetricSpectrum C K) : mappingObjectLeftUnitLaw E F :=
  RepresentedMappingEnrichment.left_unit pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction E F
    (mappingObject_left_unit_evaluation E F)

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
  · exact mappingObjectUnit_evaluation E
  · exact pointwiseTensor_triangle (mappingObject E F) E

/-- 写像対象の右単位則の等式。 -/
def mappingObjectRightUnitLaw (E F : GeneralSymmetricSpectrum C K) : Prop :=
  RepresentedMappingEnrichment.rightUnitLaw pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction E F

/-- C値写像対象の合成は右単位則を満たす。 -/
lemma mappingObject_right_unit (E F : GeneralSymmetricSpectrum C K) :
    mappingObjectRightUnitLaw E F :=
  RepresentedMappingEnrichment.right_unit pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction E F
    (mappingObject_right_unit_evaluation E F)


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
  · exact pointwiseTensor_pentagon (mappingObject G T) (mappingObject F G)
      (mappingObject E F) E

/-- C値写像対象の合成の結合則の等式。 -/
def mappingObjectAssociativityLaw (E F G T : GeneralSymmetricSpectrum C K) : Prop :=
  RepresentedMappingEnrichment.associativityLaw pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso mappingObjectFunctor
    mappingObjectAdjunction E F G T

/-- C値写像対象の合成は結合則を満たす。 -/
lemma mappingObject_associativity (E F G T : GeneralSymmetricSpectrum C K) :
    mappingObjectAssociativityLaw E F G T :=
  RepresentedMappingEnrichment.associativity pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso mappingObjectFunctor
    mappingObjectAdjunction E F G T
    (mappingObject_associativity_evaluation E F G T)


/-- 通常の射を写像対象の点へ送った後の評価の法則。 -/
def mappingObjectArrowEvaluationLaw {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F) : Prop :=
  AdjunctionHomLaws.comparisonEvaluationLaw (mappingObjectAdjunction E)
    (pointwiseTensorUnitIso E) f

/-- 射に対応する点を評価すると、作用の単位比較と元の射の合成になる。 -/
lemma mappingObjectArrow_evaluation {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F) :
    mappingObjectArrowEvaluationLaw f :=
  AdjunctionHomLaws.comparison_evaluation (mappingObjectAdjunction E)
    (pointwiseTensorUnitIso E) f

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
  · exact mappingObjectArrow_evaluation f
  · exact mappingObjectArrow_evaluation g
  · exact pointwiseTensorAssociator_parameter_naturality (mappingObjectArrow g)
      (mappingObjectArrow f) E
  · exact pointwiseTensor_triangle (𝟙_ C) E

/-- 通常の射の合成と写像対象の点の合成が一致するという法則。 -/
def mappingObjectArrowCompositionLaw {E F G : GeneralSymmetricSpectrum C K}
    (f : E ⟶ F) (g : F ⟶ G) : Prop :=
  RepresentedMappingEnrichment.arrowCompositionLaw pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction f g

/-- 通常の射の合成は写像対象の点の合成に対応する。 -/
lemma mappingObjectArrow_composition {E F G : GeneralSymmetricSpectrum C K}
    (f : E ⟶ F) (g : F ⟶ G) : mappingObjectArrowCompositionLaw f g :=
  MappingArrowComposition.represented_arrow_composition pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    (mappingObjectAdjunction E) f g (mappingObjectArrow g) (mappingObjectArrow f)
    (mappingObjectEvaluation E F) (mappingObjectEvaluation F G)
    (mappingObjectArrow_composition_evaluation f g)

/-- C-valued enrichment, with the ordinary order of composition factors. -/
@[instance_reducible]
def mappingEnrichedCategory : EnrichedCategory C (GeneralSymmetricSpectrum C K) :=
  RepresentedMappingEnrichment.enrichedCategory pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction
    mappingObject_left_unit mappingObject_right_unit mappingObject_associativity

/-- Enrichment compatible with the existing category of Sym(K) modules. -/
@[instance_reducible]
def mappingEnrichedOrdinaryCategory :
    EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  RepresentedMappingEnrichment.ordinaryCategory pointwiseTensorBifunctor
    pointwiseTensorAssociatorNatIso pointwiseTensorUnitNatIso
    mappingObjectFunctor mappingObjectAdjunction
    mappingObject_left_unit mappingObject_right_unit mappingObject_associativity
    mappingObjectArrow_identity mappingObjectArrow_composition

lemma mappingObjectArrowEquiv_eq_ordinaryHomEquiv (E F : GeneralSymmetricSpectrum C K) :
    mappingObjectArrowEquiv E F = ordinaryHomEquiv E F := rfl

lemma mappingEnrichedCategory_id (E : GeneralSymmetricSpectrum C K) :
    (mappingEnrichedCategory (K := K)).id E = mappingObjectUnit E := rfl

lemma mappingEnrichedCategory_comp (E F G : GeneralSymmetricSpectrum C K) :
    (mappingEnrichedCategory (K := K)).comp E F G =
      ReverseComposition.reverse (mappingObjectComposition E F G) := rfl

end SerrePositivity.GeneralSymmetricSpectrum
