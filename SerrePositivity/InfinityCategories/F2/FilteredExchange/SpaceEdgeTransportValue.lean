module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceEdgeValue
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointedValueTransportNaturality

/-!
概要：任意の指定空間辺の Kan 値は、既存の fiber 値比較と元の辺輸送に自然。
方針：HomotopyLimits の元の Kan 射の輸送自然性へ、同じ辺の厳密な読み戻しを入力する。
規約：値比較も指定辺も選び直さない。使われ方：native 区間表示と a6 の値の射の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の任意の空間辺の Kan 値と実際の辺輸送は、選択済みの値比較で同型に結ばれる。 -/
def spaceInfinityEdgeTransportValueIso {x y : SpaceInfinity.{u} _⦋0⦌}
    (e : SpaceInfinity.{u}.Edge x y) :
    FunctorIso ((pointedSpaceFiberValueEquivalence x).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map (spaceInfinityEdgeValue e))
      (edgeTransport pointedSpaceProjection e ≫ (pointedSpaceFiberValueEquivalence y).hom) := by
  have aux (K L : KanObject.{u}) (x y : SpaceInfinity.{u} _⦋0⦌)
      (hx : spaceInfinityVertex K = x) (hy : spaceInfinityVertex L = y)
      (e : SpaceInfinity.{u}.Edge x y) :
      FunctorIso ((pointedSpaceFiberValueEquivalence x).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (spaceInfinityEdgeValue e))
        (edgeTransport pointedSpaceProjection e ≫ (pointedSpaceFiberValueEquivalence y).hom) := by
    subst x
    subst y
    have he : HomotopyLimits.pointedRightMorphismEdge (spaceInfinityEdgeValue e) = e := by
      apply SSet.Edge.ext
      exact spaceInfinityEdgeValue_edge e
    have h := HomotopyLimits.pointedValue_transportIso (spaceInfinityEdgeValue e)
    rw [he] at h
    exact h
  exact aux (spaceInfinityObject x) (spaceInfinityObject y) x y
    (spaceInfinityVertexEquiv.apply_symm_apply x) (spaceInfinityVertexEquiv.apply_symm_apply y) e

end SerrePositivity.InfinityCategories.F2
