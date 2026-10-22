module
public import SerrePositivity.KST.Fibration.DoubleEvaluationPrecomposition
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeSectionCharts

/-! # 初頂点制限の同じ切断比較を、元の切断空間の指定成分として固定する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}}

/-- 初頂点の共同制限同型そのものを、元の実切断 Kan 値への比較として表示する。 -/
def straighteningFirstVertexSectionChart (X : LeftFibrationObject B)
    (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (leftStraighteningSectionJointDiagram_restrictIso B)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex c)) (coherentNerveVertex X))) rfl
    (congrArg HomotopyCategory.mk
      (relativeSectionDiagramInfinity_double_vertex (transportSimplexDomainFunctor B) X c))

/-- この比較は元の共同制限同型の同じ指定二重成分を保持する。 -/
theorem straighteningFirstVertexSectionChart_heq_doubleMap
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    HEq (straighteningFirstVertexSectionChart X c)
      (VertexIso.map (leftStraighteningSectionJointDiagram_restrictIso B)
        (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
          (ULift.up (nerveVertex c)) (coherentNerveVertex X))) := by
  unfold straighteningFirstVertexSectionChart F2.isoNormalizeEndpoints
  exact F2.iso_endpoints_heq _ _ _

/-- 分類写像側の元の制限同型は、同じ共同制限同型の転置の端点だけを変更する。 -/
theorem leftStraighteningInfinityMap_restrictIso_heq_transpose :
    HEq (leftStraighteningInfinityMap_restrictIso B)
      (leftStraighteningSectionJointDiagram_restrictIso B).transpose := by
  unfold leftStraighteningInfinityMap_restrictIso
  dsimp only [_root_.id]
  have hcast {α β : Sort (u + 2)} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
    cases h
    rfl
  exact hcast _ _

/-- 元の分類写像の制限成分は、同じ初頂点の切断比較の指定成分。 -/
theorem leftStraighteningInfinityMap_restrictIso_heq_sectionChart
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    HEq (VertexIso.map (leftStraighteningInfinityMap_restrictIso B)
      (kanEnrichedDoubleEvaluation X c))
      (straighteningFirstVertexSectionChart X c) := by
  let l := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B)
  let e := leftStraighteningSectionJointDiagram_restrictIso B
  have hm := F2.vertexIso_map_heq_of_heq (leftStraighteningInfinityMap_restrictIso B)
    e.transpose
    (congrArg functorVertex (transposeFunctorFamily_comp l
      (leftStraighteningSectionJointDiagram B)).symm) rfl
    (leftStraighteningInfinityMap_restrictIso_heq_transpose (B := B))
    (kanEnrichedDoubleEvaluation X c)
  exact hm.trans ((functorIso_transpose_doubleMap e (ULift.up (nerveVertex c))
    (coherentNerveVertex X)).trans
      (straighteningFirstVertexSectionChart_heq_doubleMap X c).symm)

end SerrePositivity.KST.Fibration
