module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalSourceValueTo
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedCoherentFiberComparison

/-!
概要：実頂点の値を coherent 頂点へ戻しても、同じ標準 Kan 値への射を保持する。
方針：二つの等式による fiber の移送を合成し、元の頂点等式を消去する。
規約：元の値比較を変更しない。使われ方：余極限頂点の全係数の値の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実 fiber の値射を coherent fiber へ戻すと、同じ標準値への移送となる。 -/
lemma pointedFiberValueTo_coherent_cast (K : KanObject.{u})
    {z : SpaceInfinity.{u} _⦋0⦌} (h : z = spaceInfinityVertex K) :
    eqToHom (congrArg (vertexFiber pointedSpaceProjection)
      (h.trans (spaceInfinityVertex_eq_coherent K)).symm) ≫ pointedFiberValueTo h =
    eqToHom (congrArg (vertexFiber pointedSpaceProjection)
      (spaceInfinityVertex_eq_coherent K).symm) ≫
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom := by
  rw [pointedFiberValueTo_eq_cast, ← Category.assoc, eqToHom_trans]

end SerrePositivity.InfinityCategories.F2
