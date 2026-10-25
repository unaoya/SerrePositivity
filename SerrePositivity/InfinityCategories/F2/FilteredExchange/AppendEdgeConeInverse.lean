module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.AppendEdgeConeCoordinates

/-!
概要：二終点を持つ実錐を、同じ実区間を終辺とする実錐へ戻す。
方針：元の結合同型と点二つの標準 join 同型を使う。
規約：元の全前面を保持。使われ方：合成三角形へ終点を追加する実四面体。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 二つの終点を、元の同じ実区間として束ねる射。 -/
def appendEdgeConeCoordinatesInverse (A : SSet.{u}) :
    join (join A Δ[0]) Δ[0] ⟶ join A Δ[1] :=
  (stableJoinAssociator A Δ[0] Δ[0]).hom ≫ joinMap (𝟙 A) (joinStdSimplexIso 0 0).hom

/-- 元の全錐を含む前面は、同じ実終辺の始点に沿う全面そのもの。 -/
lemma appendEdgeConeCoordinatesInverse_front (A : SSet.{u}) :
    joinInl (join A Δ[0]) Δ[0] ≫ appendEdgeConeCoordinatesInverse A =
      joinMap (𝟙 A) (stdSimplex.δ (1 : Fin 2)) := by
  rw [appendEdgeConeCoordinatesInverse, ← Category.assoc, stableJoinAssociator_inl,
    ← joinMap_comp, Category.id_comp, joinStdSimplexIso_rightPoint_inl,
    PinchedHom.front_zero]
  rfl

end SerrePositivity.InfinityCategories.F2
