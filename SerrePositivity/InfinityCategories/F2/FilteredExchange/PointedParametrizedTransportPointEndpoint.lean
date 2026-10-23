module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedParametrizedTransportPrismPoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ParametrizedTransportPointEndpoint

/-!
概要：元の全区間制限証拠の実一点終点を、元の普遍区間比較の実標的射へ一致させる。
方針：元の全作用と同じ一点評価を計算する。
規約：元の標的証拠・点・実射を保持。使われ方：元の初期値で比較を制限する前の両端照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全区間制限証拠の実一点終点は、元の普遍区間比較の同じ実標的射。 -/
lemma pointedParametrizedTransportPullback_point_endpoint {C : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : C ⟶ intervalMappingSpace x y) (l : C _⦋0⦌) :
    lift (𝟙 (vertexFiber pointedSpaceProjection x)) (SSet.const l) ≫
      (parametrizedTransportPullbackFamily pointedSpaceProjection (intervalMappingUncurry a)
        (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a)).endpoint =
    (functorVertexEquiv _ _).symm
      ((parametrizedFiberTransport pointedSpaceProjection x y).app (Opposite.op ⦋0⦌)
        (a.app (Opposite.op ⦋0⦌) l)) := by
  rw [parametrizedTransportPullbackFamily_point_endpoint]
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry a)
      (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a) = a := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [hc]

end SerrePositivity.InfinityCategories.F2
