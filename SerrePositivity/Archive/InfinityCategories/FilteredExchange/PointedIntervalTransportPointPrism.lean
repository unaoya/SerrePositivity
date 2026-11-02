module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportPoint

/-!
概要：元の区間族の同じ指定点に沿う普遍輸送の実 pointed prism を全係数で保持する。
方針：元の輸送 prism を、元の始点射と同じ指定点の組で厳密に制限する。
規約：輸送・指定点・初期値を保持。使われ方：元の全三角形の最後辺の普遍輸送化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K T : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌}
  (a : T ⟶ intervalMappingSpace x y) (l : T _⦋0⦌)
  (f : K ⟶ vertexFiber pointedSpaceProjection x)

/-- 元の始点射と指定点の組で元の実終点を制限すると、同じ実 fiber 輸送の前合成。 -/
lemma pointedIntervalTransportAt_lift_endpoint :
    lift f (SSet.const l) ≫ (pointedIntervalTransport a).endpoint =
      f ≫ pointedIntervalTransportAt a l := by
  have hn : lift f (SSet.const l) = lift (𝟙 K) (SSet.const l) ≫ (f ▷ T) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  rw [hn, Category.assoc]
  exact pointedIntervalTransportAt_pre a l f

/-- 同じ元の指定点と始点射を持つ、元の普遍輸送の実 pointed prism。 -/
def pointedIntervalTransportPointPrism : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u} :=
  (Δ[1] ◁ lift f (SSet.const l)) ≫ (pointedIntervalTransport a).prism

/-- 元の実 prism の始点は、元の始点 fiber 射の包含そのもの。 -/
lemma pointedIntervalTransportPointPrism_start :
    prismEndpoint 0 K ≫ pointedIntervalTransportPointPrism a l f =
      f ≫ vertexFiberι pointedSpaceProjection x := by
  rw [pointedIntervalTransportPointPrism, ← Category.assoc, prismEndpoint_naturality,
    Category.assoc, (pointedIntervalTransport a).start]
  simp only [← Category.assoc, lift_fst, Category.comp_id]

/-- 元の実 prism の終点は、同じ元の実 fiber 輸送の前合成の包含そのもの。 -/
lemma pointedIntervalTransportPointPrism_finish :
    prismEndpoint 1 K ≫ pointedIntervalTransportPointPrism a l f =
      (f ≫ pointedIntervalTransportAt a l) ≫ vertexFiberι pointedSpaceProjection y := by
  rw [pointedIntervalTransportPointPrism, ← Category.assoc, prismEndpoint_naturality,
    Category.assoc, (pointedIntervalTransport a).finish, ← Category.assoc,
    pointedIntervalTransportAt_lift_endpoint]

/-- 元の実 prism は、同じ指定点で制限した元の全区間族の底を厳密に被覆する。 -/
lemma pointedIntervalTransportPointPrism_projection :
    pointedIntervalTransportPointPrism a l f ≫ pointedSpaceProjection =
      (Δ[1] ◁ (SSet.const l : K ⟶ T)) ≫ intervalMappingUncurry a := by
  rw [pointedIntervalTransportPointPrism, Category.assoc, (pointedIntervalTransport a).over_base,
    ← Category.assoc, ← whiskerLeft_comp, lift_snd]

end SerrePositivity.InfinityCategories.F2
