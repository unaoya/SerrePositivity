module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroValueIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedHomTriangleEvaluationComparisons
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedValueTriangleCoefficientSquare

/-!
概要：元の零面の指定比較の値を、元の三角形と同じ全係数の評価の式で保持する。
方針：右 Hom の指定値比較の自然性で、同じ右輸送の精密化の辺を消去する。
規約：元の零面・精密化・値・評価比較を保持。使われ方：長辺値式の三因子整理。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "C" => pointedCoherentFiberComparison K ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K)))
local notation "V" => eqToHom (congrArg (vertexFiber pointedSpaceProjection)
  (Eq.symm (spaceInfinityVertex_eq_coherent L))) ≫
    QCatEquivalence.hom (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L))

/-- 元の零面の値と元の指定三角形の像は、同じ全係数の二つの評価比較で整合する。 -/
lemma spaceCompositionZero_evaluation_coherence :
    spaceCompositionZeroValueIso s V ≪≫ pointedHomTriangleLongEvaluationComparison s ≪≫
      VertexIso.map (((spaceInfinityTriangleIso s).ulift.{u, u + 1}).precomp
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom) P =
    pointedHomTriangleCompositeEvaluationComparison s := by
  rw [spaceCompositionZeroValueIso_eq_normalized]
  unfold pointedHomTriangleLongEvaluationComparison
    pointedHomTriangleCompositeEvaluationComparison
  exact iso_triangle_square_cancel
    ((pointedOppositeTriangleFunctorIso s).postcomp V)
    (pointedHomTriangleLongValueComparison s) (pointedHomTriangleCompositeValueComparison s)
    (VertexIso.map (((spaceInfinityTriangleIso s).ulift.{u, u + 1}).precomp
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom) P)
    (VertexIso.map (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 1 s))) P)
    (VertexIso.map (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
      coherentEdgeHom (SpaceInfinity.δ 0 s))) P)
    (VertexIso.map (pointedValueTriangleTransportIso s) P)
    (pointedHomTriangle_value_coherence s)
    (pointedValueTriangle_pre_square s C)

end SerrePositivity.InfinityCategories.F2
