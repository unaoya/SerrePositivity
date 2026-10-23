module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedIntervalUniversalSourceComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberTransportComparisonSourcePoint

/-!
概要：元の一点普遍比較を、同じ全初期値で制限した実二輸送の一点比較へ回収する。
方針：元の指定一点比較と、初期値制限・一点制限の交換を合成する。
規約：普遍比較を再選択しない。使われ方：元の長辺比較との同じ初期値上の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C K : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌}
  (a : C ⟶ intervalMappingSpace x y)
local notation "p" => pointedSpaceProjection
local notation "γ" => intervalMappingUncurry a
local notation "h₀" => intervalMappingUncurry_zero a
local notation "h₁" => intervalMappingUncurry_one a
local notation "T" => pointedIntervalTransport a
local notation "U" => parametrizedTransportPullbackFamily p γ h₀ h₁

/-- 元の全初期値での一点普遍比較は、同じ実二輸送の初期値制限の一点比較。 -/
lemma pointedIntervalTransportAt_universalIso_precomp_heq_source_endpoint [Quasicategory C]
    (l : C _⦋0⦌) (f : K ⟶ vertexFiber p x) :
    HEq ((pointedIntervalTransportAt_universalIso a l).precomp f)
      ((((T).precomposeSource f).endpointIso p (f ≫ 𝟙 _) γ h₁
        ((U).precomposeSource f)).precomp (lift (𝟙 K) (SSet.const l))) := by
  exact (pointedIntervalTransportAt_universalIso_precomp_heq_endpoint a l f).trans
    (fiberTransportFamily_endpointIso_precomposeSource_point p (𝟙 _) γ h₁ T U f l)

end SerrePositivity.InfinityCategories.F2
