module

public import SerrePositivity.InfinityCategories.F2.PointedIntervalTransportUniversal
public import SerrePositivity.InfinityCategories.F2.ChosenTransportSourceComparison

/-!
概要：元の指定区間の普遍比較を、同じ選択済み輸送族の全区間への直接比較へ戻す。
方針：元の端点表示変更を除き、恒等係数の自己比較因子を消去する。
規約：元の指定比較を保持。使われ方：指定一点区間と第二の普遍 prism の値の橋渡し。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {T : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌}
  (a : T ⟶ intervalMappingSpace x y)

/-- 元の指定区間の普遍比較は、同じ恒等初期係数の全比較の指定値を保持する。 -/
lemma pointedIntervalTransport_mapIso_heq_parametrizedSource :
    HEq (pointedIntervalTransport_mapIso a)
      (FiberTransportFamily.mapIso_parametrizedSource pointedSpaceProjection (𝟙 _)
        (intervalMappingUncurry a) (intervalMappingUncurry_zero a)
        (intervalMappingUncurry_one a) (pointedIntervalTransport a)) := by
  unfold pointedIntervalTransport_mapIso
  have hcast {α β : Sort (u + 2)} (h : α = β) (z : α) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  exact (hcast _ _).trans (hcast _ _)

/-- 元の指定区間の普遍比較は、同じ選択済み輸送族から全区間への直接比較と同じ値。 -/
lemma pointedIntervalTransport_mapIso_heq_direct :
    HEq (pointedIntervalTransport_mapIso a)
      (FiberTransportFamily.mapIso_parametrized pointedSpaceProjection
        (intervalMappingUncurry a) (intervalMappingUncurry_zero a)
        (intervalMappingUncurry_one a) (pointedIntervalTransport a)) :=
  (pointedIntervalTransport_mapIso_heq_parametrizedSource a).trans
    (chosenTransport_parametrizedSource_heq_direct pointedSpaceProjection
      (intervalMappingUncurry a) (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a))

end SerrePositivity.InfinityCategories.F2
