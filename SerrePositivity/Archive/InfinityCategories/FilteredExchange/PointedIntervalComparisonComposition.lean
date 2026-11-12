module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointedIntervalTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportFamilyComparisonComposition

/-!
概要：元の区間の普遍 pointed 輸送との比較から、中間の指定輸送を厳密に消去する。
方針：既存の普遍比較を同じ三輸送の指定 endpointIso の合成則へ戻す。
規約：元の区間と全係数を保持。使われ方：定値作用と下側輸送因子の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ区間・同じ始点の指定輸送を経由しても、元の普遍輸送への指定比較と一致する。 -/
lemma pointedIntervalTransportComparison_trans {K T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (f : K ⟶ vertexFiber pointedSpaceProjection x)
    (a : T ⟶ intervalMappingSpace x y)
    (w v : FiberTransportFamily (b := y) pointedSpaceProjection f (intervalMappingUncurry a)) :
    w.endpointIso pointedSpaceProjection f (intervalMappingUncurry a)
        (intervalMappingUncurry_one a) v ≪≫ pointedIntervalTransportComparison f a v =
      pointedIntervalTransportComparison f a w := by
  unfold pointedIntervalTransportComparison
  apply fiberTransportFamily_endpointIso_trans

end SerrePositivity.InfinityCategories.F2
