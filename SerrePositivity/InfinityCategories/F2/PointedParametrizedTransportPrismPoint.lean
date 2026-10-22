module

public import SerrePositivity.InfinityCategories.F2.ParametrizedTransportPullbackFamily
public import SerrePositivity.InfinityCategories.F2.PointedIntervalTransportPointPrism

/-!
概要：指定区間比較の実第二 prism の同じ一点制限を、元の実対角普遍 prism に戻す。
方針：元の標的証拠の実対角式と、元の区間の curry の往復を計算する。
規約：元の実 prism と全初期値を保持。使われ方：元の長辺との比較の第二 prism の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定区間の実標的 prism の同じ一点制限は、元の同じ実対角普遍 prism。 -/
lemma pointedParametrizedTransportPullback_point_prism {C Q : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : C ⟶ intervalMappingSpace x y) (l : C _⦋0⦌)
    (f : Q ⟶ vertexFiber pointedSpaceProjection x) :
    (Δ[1] ◁ lift f (SSet.const l)) ≫
      (parametrizedTransportPullbackFamily pointedSpaceProjection (intervalMappingUncurry a)
        (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a)).prism =
      diagonalUniversalPrism pointedSpaceProjection f (SSet.const (a.app (Opposite.op ⦋0⦌) l)) := by
  rw [parametrizedTransportPullbackFamily_diagonal_prism]
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry a)
      (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a) = a := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [hc, SSet.const_comp]

end SerrePositivity.InfinityCategories.F2
