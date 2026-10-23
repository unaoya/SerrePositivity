module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedOppositeRefinementEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroEndpointNormalized

/-!
概要：元の反転精密化の全作用の値を、指定三角形作用の値そのものへ同定する。
方針：元の両面による頂点の等式を保持して、同じ異種等式に値写像を適用する。
規約：元の値と指定された類を保持。使われ方：長辺値式の元の比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "A" => spaceSimplexPointedCoefficients s

/-- 同じ全作用の指定精密化の値は、元の二段作用から長辺作用への同型の後合成。 -/
lemma pointedOppositeRefinement_value_heq_normalized {Z : SSet.{u + 1}}
    (V : vertexFiber pointedSpaceProjection (coherentNerveVertex L) ⟶ Z) :
    HEq (VertexIso.map (coherentKanOppositeRefinementIso K L (coherentTriangleHomotopy s))
      (pointedOppositeHomAction K L ≫ (ihom A).map V))
      ((pointedOppositeTriangleFunctorIso s).postcomp V) := by
  rw [← vertexIso_map_comp]
  have hm := vertexIso_map_heq_of_heq
    (VertexIso.map (coherentKanOppositeRefinementIso K L (coherentTriangleHomotopy s))
      (pointedOppositeHomAction K L)) (pointedOppositeTriangleFunctorIso s)
    ((pointedOppositeRefinementAction_source_eq_triangle s).trans
      (pointedOppositeTriangleAction_source_vertex s))
    ((pointedOppositeRefinementAction_target_eq_triangle s).trans
      (pointedOppositeTriangleAction_target_vertex s))
    (pointedOppositeRefinementAction_heq_normalized s) ((ihom A).map V)
  exact hm.trans (functorIso_postcomp_vertexMap_heq (pointedOppositeTriangleFunctorIso s) V).symm

end SerrePositivity.InfinityCategories.F2
