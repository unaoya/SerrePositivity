module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceEdgeValue
public import SerrePositivity.InfinityCategories.F1.UniversalTransportReflection
public import SerrePositivity.InfinityCategories.F1.InvertibleLeftTransport

/-!
概要：元の可逆な空間辺の同じ Kan 値の射は同値。
方針：元の全辺を coherent 辺へ読み戻し、普遍 pointed 輸送による判定を使う。
規約：指定辺の両端と全一単体を保持。使われ方：余極限余錐間の点回収の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の可逆な空間辺を読み戻した同じ Kan 射は quasicategory の同値。 -/
lemma spaceInfinityEdgeValue_isQCatEquivalence {x y : SpaceInfinity.{u} _⦋0⦌}
    (e : SpaceInfinity.{u}.Edge x y) (he : IsInvertibleEdge e) :
    IsQCatEquivalence (spaceInfinityEdgeValue e) := by
  have ht := edgeTransport_isQCatEquivalence_of_isInvertibleEdge pointedSpaceProjection e he
  have hc := (edgeTransport_isQCatEquivalence_congr_edge pointedSpaceProjection e
    (coherentNerveEdge (spaceInfinityEdgeValue e)) (spaceInfinityEdgeValue_edge e).symm).mp ht
  exact (pointedSpaceTransport_coherentEdge_isQCatEquivalence_iff _).mp hc

end SerrePositivity.InfinityCategories.F2.Compact
