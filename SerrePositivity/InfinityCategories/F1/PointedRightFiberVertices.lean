module

public import SerrePositivity.InfinityCategories.F1.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.F1.PointFunctorEvaluationVertices
public import SerrePositivity.InfinityCategories.F1.PointedReverseFiberVertices
public import SerrePositivity.InfinityCategories.F1.PointedRightIntervalIdentity
public import SerrePositivity.InfinityCategories.F1.CoherentKanRightCompositionTransport

/-!
概要：右 Hom の一点係数から、指定された元の pointed fiber の頂点を回収する。
方針：左右の区間比較の零単体を同じ辺に同定し、coslice 全体の恒等則を使う。
規約：元の Kan 空間と反対空間を同一視しない。
使われ方：右 Hom の点評価と相対 coherent recovery の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の点からの右区間は、その pointed 頂点の coslice の辺と厳密に一致する。 -/
lemma pointedRightFiberComparison_interval_vertex (K : KanObject.{u})
    (s : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌) :
    ((SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv ≫
      coherentKanRightHomInterval pointKanObject K).app (Opposite.op ⦋0⦌)
        (ULift.up (pointedSpaceFiberVertexEquiv K s)) =
      (cosliceFiberToIntervalMappingSpace pointSpaceVertex (spaceInfinityVertex K)).app _ s := by
  change (intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
    (coherentNerveVertex pointKanObject) (coherentNerveVertex K)
    (spaceInfinityVertex_eq_coherent pointKanObject).symm
    (spaceInfinityVertex_eq_coherent K).symm).app _
      ((pinchedHomToIntervalMappingSpace (coherentNerveVertex pointKanObject)
        (coherentNerveVertex K)).app _
        ((coherentHomComparison pointKanObject K).app _
          (ULift.up ((pointFunctorEvaluationIso K.obj).inv.app _
            (pointedSpaceFiberVertexEquiv K s))))) = _
  rw [pointFunctorEvaluationIso_inv_vertex, pinchedHomToIntervalMappingSpace_vertex,
    intervalMappingPostOfEq_vertex, cosliceFiberToIntervalMappingSpace_vertex]
  apply congrArg intervalMappingVertexOfEdge
  apply SSet.Edge.ext
  change coherentHomComparisonSimplex (C := KanObject.{u}) (X := pointKanObject) (Y := K)
    (functorVertex (SSet.yonedaEquiv.symm (pointedSpaceFiberVertexEquiv K s))) =
      (cosliceFiberVertexToEdge s).edge
  rw [coherentHomComparisonSimplex_zero_edge (C := KanObject.{u})]
  change (coherentNerveEdge (C := KanObject.{u}) (X := pointKanObject) (Y := K)
    (SSet.yonedaEquiv.symm (pointedSpaceFiberVertexEquiv K s))).edge = _
  rw [pointedSpaceFiberVertexEquiv_edge, Equiv.symm_apply_apply]
  exact congrArg SSet.Edge.edge (coherentNerveEdge_hom _)

/-- 右 Hom の fiber 比較で元の点を戻すと、指定された実際の pointed 頂点と同型。 -/
def pointedRightFiberComparison_vertexIso (K : KanObject.{u})
    (s : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌) :
    VertexIso
      ((pointedRightFiberComparison K).app (Opposite.op ⦋0⦌)
        (ULift.up (pointedSpaceFiberVertexEquiv K s))) s := by
  have h := pointedRightFiberComparison_interval_vertex K s
  have e := (pointedRightIntervalEvaluate_cosliceIso (spaceInfinityVertex K)).app s
  change VertexIso
    ((pointedRightIntervalEvaluate (spaceInfinityVertex K)).app (Opposite.op ⦋0⦌)
      (((SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv ≫
        coherentKanRightHomInterval pointKanObject K).app (Opposite.op ⦋0⦌)
        (ULift.up (pointedSpaceFiberVertexEquiv K s)))) s
  rw [h]
  exact e

end SerrePositivity.InfinityCategories
