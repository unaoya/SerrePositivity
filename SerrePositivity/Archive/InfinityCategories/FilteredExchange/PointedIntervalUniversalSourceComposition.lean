module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalUniversalSourceEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportFamilyComparisonComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：元の全初期値での実輸送比較と指定一点普遍比較を、同じ直接比較へ合成する。
方針：元の普遍比較を同じ実二 prism の比較へ戻し、選択済み輸送を消去する。
規約：元の指定比較を保持。使われ方：長辺の実比較と native 比較の値の照合。
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

/-- 元の選択済み輸送を中間因子として消去する、同じ全初期値上の指定値の合成。 -/
lemma pointedIntervalUniversalSource_comparison_trans [Quasicategory C]
    (l : C _⦋0⦌) (f : K ⟶ vertexFiber p x)
    (W : FiberTransportFamily (b := y) p (f ≫ 𝟙 _) γ) :
    (W.endpointIso p (f ≫ 𝟙 _) γ h₁ ((T).precomposeSource f)).precomp
        (lift (𝟙 K) (SSet.const l)) ≪≫
      functorIsoOfEq ((pointedIntervalTransportAt_universalIso a l).precomp f)
        (pointedIntervalTransportAt_pre a l f).symm
        (by
          rw [fiberTransportFamily_precomposeSource_point_endpoint,
            pointedParametrizedTransportPullback_point_endpoint]) =
    (W.endpointIso p (f ≫ 𝟙 _) γ h₁ ((U).precomposeSource f)).precomp
      (lift (𝟙 K) (SSet.const l)) := by
  let e := (pointedIntervalTransportAt_universalIso a l).precomp f
  have he := pointedIntervalTransportAt_universalIso_precomp_heq_source_endpoint a l f
  have hs := (pointedIntervalTransportAt_pre a l f).symm
  have ht : f ≫ (functorVertexEquiv _ _).symm
      ((parametrizedFiberTransport p x y).app (Opposite.op ⦋0⦌)
        (a.app (Opposite.op ⦋0⦌) l)) =
      lift (𝟙 K) (SSet.const l) ≫ ((U).precomposeSource f).endpoint := by
    rw [fiberTransportFamily_precomposeSource_point_endpoint,
      pointedParametrizedTransportPullback_point_endpoint]
  have hc := eq_of_heq ((functorIsoOfEq_heq e hs ht).trans he)
  change _ ≪≫ functorIsoOfEq e hs ht = _
  rw [hc, ← functorIso_precomp_trans, fiberTransportFamily_endpointIso_trans]

end SerrePositivity.InfinityCategories.F2
