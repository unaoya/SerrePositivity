module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointedIntervalTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCurryPointVertex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedFiberValueTo

/-!
概要：元の区間族の指定点での普遍輸送を、同じ実終点の指定係数制限として計算する。
方針：元の map の同じ零単体を実射へ戻し、元の curry の一点式を使う。
規約：元の輸送・係数・終点等式を保持。使われ方：残る二面比較の実 fiber 後合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の普遍輸送の同じ指定点の零単体から得る実 fiber 射。 -/
def pointedIntervalTransportAt {T : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌}
    (a : T ⟶ intervalMappingSpace x y) (l : T _⦋0⦌) :=
  (functorVertexEquiv _ _).symm ((pointedIntervalTransport a).map.app (Opposite.op ⦋0⦌) l)

/-- 元の指定点での実 fiber 射は、同じ係数で制限した元の実終点そのもの。 -/
lemma pointedIntervalTransportAt_eq_restriction {T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : T ⟶ intervalMappingSpace x y) (l : T _⦋0⦌) :
    lift (𝟙 _) (SSet.const l) ≫ (pointedIntervalTransport a).endpoint =
      pointedIntervalTransportAt a l := by
  apply functorVertex_injective
  exact (functorCurry_point_vertex (pointedIntervalTransport a).endpoint l).symm.trans
    ((functorVertexEquiv _ _).apply_symm_apply _).symm

/-- 同じ点への実制限は、元の始点 fiber 射の前合成とも厳密に可換する。 -/
lemma pointedIntervalTransportAt_pre {K T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : T ⟶ intervalMappingSpace x y) (l : T _⦋0⦌)
    (f : K ⟶ vertexFiber pointedSpaceProjection x) :
    lift (𝟙 K) (SSet.const l) ≫ (f ▷ T) ≫ (pointedIntervalTransport a).endpoint =
      f ≫ pointedIntervalTransportAt a l := by
  have hn : lift (𝟙 K) (SSet.const l) ≫ (f ▷ T) =
      f ≫ lift (𝟙 _) (SSet.const l) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  rw [← Category.assoc, hn, Category.assoc, pointedIntervalTransportAt_eq_restriction]

/-- raw/native の同じ区間族を同じ点で評価した値は、同じ固定標的値の中で一致する。 -/
lemma pointedIntervalTransportAt_valueTo_eq {T : SSet.{u + 1}}
    {x y y' : SpaceInfinity.{u} _⦋0⦌} (hy : y = y')
    (a : T ⟶ intervalMappingSpace x y) (a' : T ⟶ intervalMappingSpace x y')
    (ha : HEq a a') (l : T _⦋0⦌) :
    pointedIntervalTransportAt a l ≫ pointedFiberValueTo hy =
      pointedIntervalTransportAt a' l ≫ (pointedSpaceFiberValueEquivalence y').hom := by
  cases hy
  cases eq_of_heq ha
  rfl

end SerrePositivity.InfinityCategories.F2
