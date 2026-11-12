module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalUniversalPrismComponent
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedParametrizedTransportPointEndpoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：元の指定一点区間の普遍比較を、元の任意の全初期値で制限して同じ比較へ戻す。
方針：実両端の一致を保って同じ前合成を適用し、二段の係数制限を合わせる。
規約：元の指定比較・初期値を保持。使われ方：元の長辺の初期値 q への適用。
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
local notation "e" => FiberTransportFamily.endpointIso p (𝟙 _) γ h₁ T U

/-- 元の普遍一点比較を元の全初期値で制限しても、同じ実二 prism の指定値を保つ。 -/
lemma pointedIntervalTransportAt_universalIso_precomp_heq_endpoint [Quasicategory C]
    (l : C _⦋0⦌) (f : K ⟶ vertexFiber p x) :
    HEq ((pointedIntervalTransportAt_universalIso a l).precomp f)
      (FunctorIso.precomp e (lift f (SSet.const l))) := by
  let j := lift (𝟙 (vertexFiber p x)) (SSet.const l)
  have he := functorIso_precomp_heq_of_heq (FunctorIso.precomp e j)
    (pointedIntervalTransportAt_universalIso a l)
    (pointedIntervalTransportAt_eq_restriction a l)
    (pointedParametrizedTransportPullback_point_endpoint a l)
    (pointedIntervalTransportAt_universalIso_heq_endpoint a l) f
  have hj : f ≫ j = lift f (SSet.const l) := by
    rw [comp_lift, Category.comp_id, SSet.comp_const]
  exact he.trans ((heq_of_eq (functorIso_precomp_precomp e j f)).trans
    (functorIso_precomp_heq_of_map_eq e hj))

end SerrePositivity.InfinityCategories.F2
