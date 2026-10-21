module

public import SerrePositivity.InfinityCategories.F1.InnerTwoHornOverPushout
public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackNativeCorePushout
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramPushout

/-!
概要：同じ共有頂点で貼った二区間に対する、分類 Hom の両側の厳密な pullback。
方針：同じホーンの底上の pushout に、元の Hom と区間 Hom の貼り合わせを適用する。
規約：底上の元の二包含と二つの頂点の制限を、そのまま二射影と下辺にする。
使われ方：二次元単体上の元の分類 Hom 作用の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
namespace InnerTwoHornOver

/-- 二つの区間上の元の Hom の core は、同じ共有頂点上の厳密な pullback。 -/
lemma nativeCore_isPullback {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
    (h : (Λ[2, 1] : SSet.{u}) ⟶ B) :
    IsPullback
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q (secondInclusion h)))
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q (firstInclusion h)))
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q (toSecond h)))
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q (toFirst h))) :=
  core_cocartesianPullbackNativePre_isPullback_of_isPushout p q
    (toFirst h) (toSecond h) (firstInclusion h) (secondInclusion h) (isPushout h)

/-- 分類先の同じ区間 Hom も、同じ共有頂点上の厳密な pullback。 -/
lemma intervalDiagram_isPullback {B X : SSet.{u}} (F G : B ⟶ X)
    (h : (Λ[2, 1] : SSet.{u}) ⟶ B) :
    IsPullback (intervalDiagramOverPre F G (secondInclusion h))
      (intervalDiagramOverPre F G (firstInclusion h))
      (intervalDiagramOverPre F G (toSecond h))
      (intervalDiagramOverPre F G (toFirst h)) :=
  intervalDiagramOverPre_isPullback_of_isPushout F G
    (toFirst h) (toSecond h) (firstInclusion h) (secondInclusion h) (isPushout h)

end InnerTwoHornOver
end SerrePositivity.InfinityCategories
