module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueTriangleSquare
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IsoTriangleSquareCancellation

/-!
概要：元の右 Hom の値の三角形正方形を、任意の同じ初期係数で読む。
方針：元の四同型の正方形を同じ前合成射で写す。
規約：指定精密化・全係数・値を保持。使われ方：零面の値の精密化の消去。
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

/-- 同じ全初期係数での元の三角形・両端比較・右輸送の正方形。 -/
lemma pointedValueTriangle_pre_square {P : SSet.{u + 1}}
    (q : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) :
    let m := (pre q).app ((SSet.uliftFunctor.{u + 1, u}).obj (L).obj)
    VertexIso.map (((spaceInfinityTriangleIso s).ulift.{u, u + 1}).precomp
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom) m ≪≫
      VertexIso.map (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
        coherentEdgeHom (SpaceInfinity.δ 0 s))) m =
    VertexIso.map (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 1 s))) m ≪≫
      VertexIso.map (pointedValueTriangleTransportIso s) m := by
  exact vertexIso_map_square
    (((spaceInfinityTriangleIso s).ulift.{u, u + 1}).precomp
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom)
    (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
      coherentEdgeHom (SpaceInfinity.δ 0 s)))
    (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 1 s)))
    (pointedValueTriangleTransportIso s)
    ((pre q).app ((SSet.uliftFunctor.{u + 1, u}).obj (L).obj))
    (pointedValueTriangle_isoSquare s)

end SerrePositivity.InfinityCategories.F2
