module

public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldBridgeOverPushout
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeCorePushout
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeLiftRestriction
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramPushout
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePullbacks

/-!
概要：最初の区間と尾部上で、元の Hom と分類先の Hom を同じ厳密な pullback に表示する。
方針：同じ底上の pushout に両側の貼り合わせを適用する。
規約：共有頂点と二つの元の制限をそのまま射影に使う。
使われ方：高次単体の元の分類 Hom 作用の二成分比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
namespace ScaffoldBridgeOver

variable (n : ℕ) {B : SSet.{u}}
  (h : pushout (stdSimplex.δ (0 : Fin 2))
    (nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ⟶ B)

/-- 同じ二成分上の元の native Hom の core は厳密な pullback。 -/
lemma nativeCore_isPullback {E F : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q] :
    IsPullback
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q (firstInclusion n h)))
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q (tailInclusion n h)))
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q (toFirst n h)))
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q (toTail n h))) :=
  (core_cocartesianPullbackNativePre_isPullback_of_isPushout p q
    (toFirst n h) (toTail n h) (firstInclusion n h) (tailInclusion n h) (isPushout n h)).flip

/-- 分類先と同じ宇宙へ移しても、同じ元の native core は厳密な pullback。 -/
lemma nativeLift_isPullback {E F : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q] :
    IsPullback (cocartesianPullbackNativeLiftPre p q (firstInclusion n h))
      (cocartesianPullbackNativeLiftPre p q (tailInclusion n h))
      (cocartesianPullbackNativeLiftPre p q (toFirst n h))
      (cocartesianPullbackNativeLiftPre p q (toTail n h)) :=
  (nativeCore_isPullback n h p q).map (SSet.uliftFunctor.{u + 1, u})

/-- 分類先の同じ両端固定区間 Hom も厳密な pullback。 -/
lemma intervalDiagram_isPullback {X : SSet.{u}} (P Q : B ⟶ X) :
    IsPullback (intervalDiagramOverPre P Q (firstInclusion n h))
      (intervalDiagramOverPre P Q (tailInclusion n h))
      (intervalDiagramOverPre P Q (toFirst n h))
      (intervalDiagramOverPre P Q (toTail n h)) :=
  (intervalDiagramOverPre_isPullback_of_isPushout P Q
    (toFirst n h) (toTail n h) (firstInclusion n h) (tailInclusion n h) (isPushout n h)).flip

end ScaffoldBridgeOver
end SerrePositivity.InfinityCategories
