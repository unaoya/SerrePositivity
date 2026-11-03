module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalUniversalComparisonPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ParametrizedTransportComparisonPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportAtUniversalIso

/-!
概要：元の指定一点区間の普遍比較を、同じ実二 prism の指定 endpointIso へ回収する。
方針：同じ元の全比較の一点成分を取り、実標的への比較の同じ係数制限と同定する。
規約：元の指定比較を保持。使われ方：第二の普遍 prism と元の実長辺の比較の橋渡し。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌}
  (a : C ⟶ intervalMappingSpace x y)
local notation "p" => pointedSpaceProjection
local notation "γ" => intervalMappingUncurry a
local notation "h₀" => intervalMappingUncurry_zero a
local notation "h₁" => intervalMappingUncurry_one a
local notation "T" => pointedIntervalTransport a
local notation "U" => parametrizedTransportPullbackFamily p γ h₀ h₁
local notation "e" => FiberTransportFamily.endpointIso p (𝟙 _) γ h₁ T U

/-- 元の指定一点区間の普遍比較は、同じ実二 prism の指定比較の同じ係数制限。 -/
lemma pointedIntervalTransportAt_universalIso_heq_endpoint [Quasicategory C]
    (l : C _⦋0⦌) :
    HEq (pointedIntervalTransportAt_universalIso a l)
      (FunctorIso.precomp e (lift (𝟙 (vertexFiber p x)) (SSet.const l))) := by
  have hc : intervalMappingCurryOfEndpoints γ h₀ h₁ = a := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁
  have he := functorIso_app_heq_of_heq (pointedIntervalTransport_mapIso a)
    (FiberTransportFamily.mapIso_parametrized p γ h₀ h₁ T) rfl (by rw [hc])
    (pointedIntervalTransport_mapIso_heq_direct a) l
  exact (pointedIntervalTransportAt_universalIso_heq_app a l).trans
    (he.trans (fiberTransportFamily_parametrized_app_heq_endpoint p γ h₀ h₁ T l))

end SerrePositivity.InfinityCategories.F2
