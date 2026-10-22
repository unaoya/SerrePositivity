module

public import SerrePositivity.InfinityCategories.F2.PointedOppositeRefinementAction

/-!
概要：元の反転精密化の作用の両端を、元の三角形の同じ両端へ戻す。
方針：元の精密化の両面と Kan 射の頂点の式を使う。
規約：同型の異種等式から頂点等式を取り出さない。使われ方：値の像の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))

/-- 元の反転精密化の作用の実始点は元の二辺合成での同じ作用の頂点。 -/
lemma pointedOppositeRefinementAction_source_eq_triangle :
    (pointedOppositeHomAction K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm
        ((SimplicialCategory.sHom K L).δ 0 (coherentTriangleHomotopy s)))) =
    (pointedOppositeHomAction K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (functorVertex
        (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫ coherentEdgeHom (SpaceInfinity.δ 0 s))))) := by
  rw [coherentTriangleHomotopy_target, kanHom_vertex]
  rfl

/-- 元の反転精密化の作用の実終点は元の長辺での同じ作用の頂点。 -/
lemma pointedOppositeRefinementAction_target_eq_triangle :
    (pointedOppositeHomAction K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm
        ((SimplicialCategory.sHom K L).δ 1 (coherentTriangleHomotopy s)))) =
    (pointedOppositeHomAction K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm
        (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s))))) := by
  rw [coherentTriangleHomotopy_source, kanHom_vertex]
  rfl

end SerrePositivity.InfinityCategories.F2
