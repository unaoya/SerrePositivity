module
public import SerrePositivity.KST.Fibration.FirstVertexDiagramComponent
public import SerrePositivity.KST.Fibration.DoubleEvaluationPrecompositionVertices

/-! # 共通 Hom 解像上でも、元の初頂点制限の同じ指定成分を保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]

/-- 元の射影を共通 Hom 解像の同じ対象として表示する。 -/
def firstVertexComparisonObject : EdgewiseEnrichedObject (LeftFibrationObject B) :=
  ⟨leftFibrationObjectOf p, trivial⟩

/-- 解像の同じ指定対象を射影すると、元の射影の頂点そのもの。 -/
theorem firstVertexComparisonObject_projection_vertex :
    (edgewiseEnrichedInfinityMap (LeftFibrationObject B)).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex (firstVertexComparisonObject p)) = leftFibrationInfinityVertex p :=
  coherentNerveMap_vertex (edgewiseEnrichedRight (LeftFibrationObject B)) _

/-- 共通解像での制限の始域値は、元の共同分類値。 -/
theorem firstVertexEdgewiseRestriction_source_vertex (c : TransportSimplexCategory B) :
    (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation (firstVertexComparisonObject p) c).app (Opposite.op ⦋0⦌)
        (functorVertex (edgewiseEnrichedInfinityMap (LeftFibrationObject B) ≫
          (leftStraighteningInfinityMap B ≫
            (pre ((SSet.uliftFunctor.{u + 1, u}).map
              (transportSimplexFirstVertexMap B))).app SpaceInfinity.{u}))) =
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex c)) (leftFibrationInfinityVertex p)).app (Opposite.op ⦋0⦌)
          (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            (transportSimplexFirstVertexMap B) ≫ leftStraighteningSectionJointDiagram B)) := by
  exact (doubleFunctorEvaluation_precomp_vertex_of_eq
    (leftStraighteningInfinityMap B ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (transportSimplexFirstVertexMap B))).app SpaceInfinity.{u})
    (edgewiseEnrichedInfinityMap (LeftFibrationObject B))
    (coherentNerveVertex (firstVertexComparisonObject p)) (ULift.up (nerveVertex c))
    (leftFibrationInfinityVertex p) (firstVertexComparisonObject_projection_vertex p)).trans
      (straighteningRestrict_source_vertex (leftFibrationObjectOf p) c)

/-- 共通解像での制限の終域値は、元の pullback strict 切断空間。 -/
theorem firstVertexEdgewiseRestriction_target_vertex (c : TransportSimplexCategory B) :
    (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation (firstVertexComparisonObject p) c).app (Opposite.op ⦋0⦌)
        (functorVertex (edgewiseEnrichedInfinityMap (LeftFibrationObject B) ≫
          (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
            leftStraighteningCoherentMap (TransportSimplexCategory B)))) =
      spaceInfinityVertex ((((relativeSectionEnrichedDiagram (strictTransportDomains
        (TransportSimplexCategory B))).precompose
          (leftFibrationBaseChangeEnriched (transportSimplexFirstVertexMap B))).obj c).obj
            (leftFibrationObjectOf p)) := by
  exact (doubleFunctorEvaluation_precomp_vertex_of_eq
    (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
      leftStraighteningCoherentMap (TransportSimplexCategory B))
    (edgewiseEnrichedInfinityMap (LeftFibrationObject B))
    (coherentNerveVertex (firstVertexComparisonObject p)) (ULift.up (nerveVertex c))
    (leftFibrationInfinityVertex p) (firstVertexComparisonObject_projection_vertex p)).trans
      (transportUnderBaseChange_source_vertex (leftFibrationObjectOf p) c)

/-- 元の解像上の制限同型の同じ指定成分を、元の切断空間へ表示する。 -/
def firstVertexEdgewiseRestrictionChart (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map ((leftStraighteningInfinityMap_firstVertexRestrictionIso B).precomp
      (edgewiseEnrichedInfinityMap (LeftFibrationObject B)))
      (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation (firstVertexComparisonObject p) c))
    (congrArg HomotopyCategory.mk (firstVertexEdgewiseRestriction_source_vertex p c))
    (congrArg HomotopyCategory.mk (firstVertexEdgewiseRestriction_target_vertex p c))

/-- 解像上でも、元の同じ初頂点制限の指定成分に厳密一致する。 -/
theorem firstVertexEdgewiseRestrictionChart_eq (c : TransportSimplexCategory B) :
    firstVertexEdgewiseRestrictionChart p c =
      firstVertexRestrictionChart (leftFibrationObjectOf p) c := by
  have hm := functorIso_pre_doubleMap_of_vertex
    (leftStraighteningInfinityMap_firstVertexRestrictionIso B)
    (edgewiseEnrichedInfinityMap (LeftFibrationObject B))
    (coherentNerveVertex (firstVertexComparisonObject p)) (ULift.up (nerveVertex c))
    (leftFibrationInfinityVertex p) (firstVertexComparisonObject_projection_vertex p)
  exact F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    (hm.trans (firstVertexRestrictionChart_heq_doubleMap (leftFibrationObjectOf p) c).symm)

end SerrePositivity.KST.Fibration
