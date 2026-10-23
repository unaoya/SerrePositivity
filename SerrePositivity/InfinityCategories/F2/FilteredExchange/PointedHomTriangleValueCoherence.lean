module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedHomTriangleValueComparisons
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoFourFactorReplaceEdges

/-!
概要：元の coherent 三角形の指定作用と指定右輸送は、同じ全係数の値で整合する。
方針：一般精密化の整合式の両外辺を、同じ元の三角形の指定同型へ戻す。
規約：元の精密化・値・両端比較を保持。使われ方：長辺値式の指定因子の照合。
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
local notation "H" => SimplicialCategory.sHom K L
local notation "e" => coherentTriangleHomotopy s
local notation "A" => spaceSimplexPointedCoefficients s
local notation "C" => pointedCoherentFiberComparison K ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K)))
local notation "V" => eqToHom (congrArg (vertexFiber pointedSpaceProjection)
  (Eq.symm (spaceInfinityVertex_eq_coherent L))) ≫
    QCatEquivalence.hom (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L))
local notation "η" => pointedLeftHomValueActionIso K L
local notation "l" => ULift.up (SSet.opObjEquiv.symm (SimplicialObject.δ H 1 e))
local notation "c" => ULift.up (SSet.opObjEquiv.symm (SimplicialObject.δ H 0 e))

/-- 元の指定三角形の反転作用・右輸送・全係数比較は同じ値の式を満たす。 -/
lemma pointedHomTriangle_value_coherence :
    (pointedOppositeTriangleFunctorIso s).postcomp V ≪≫
        pointedHomTriangleLongValueComparison s ≪≫
        VertexIso.map (pointedValueTriangleTransportIso s) P =
      pointedHomTriangleCompositeValueComparison s := by
  exact vertexIso_four_factor_replace_edges
    (VertexIso.map (coherentKanOppositeRefinementIso K L e)
      (pointedOppositeHomAction K L ≫ (ihom A).map V))
    (FunctorIso.app η l)
    (VertexIso.map (VertexIso.map (coherentKanRefinementSourceComparison K L e)
      (pointedIntervalValueAction K L)) P)
    (VertexIso.map (VertexIso.map (coherentKanRightRefinementIso K L e)
      (pointedIntervalValueAction K L)) P)
    (FunctorIso.app η c ≪≫
      VertexIso.map (VertexIso.map (coherentKanRefinementTargetComparison K L e)
        (pointedIntervalValueAction K L)) P)
    ((pointedOppositeTriangleFunctorIso s).postcomp V)
    (VertexIso.map (pointedValueTriangleTransportIso s) P)
    (pointedOppositeRefinementValue_source_vertex s V)
    (pointedOppositeRefinementValue_target_vertex s V)
    (congrArg (NatTrans.app P (Opposite.op ⦋0⦌))
      (pointedRightRefinementValue_source_eq_triangle s))
    (congrArg (NatTrans.app P (Opposite.op ⦋0⦌))
      (pointedRightRefinementValue_target_eq_triangle s))
    (pointedOppositeRefinement_value_heq_normalized s V)
    (pointedRightRefinement_value_pre_heq_triangle s C)
    (pointedHomRefinement_value_coherence K L e)

end SerrePositivity.InfinityCategories.F2
