module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldStandardSourceComponents
public import SerrePositivity.InfinityCategories.F1.Joins.SpanPullbackIsomorphism
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldBridgeHomPullbacks
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePullbacks

/-!
概要：元の source pullback と同じ小さい同じ貼合せの native core pullback を同型で結ぶ。
方針：同じ三つの表示同型を作用させ、元の core の厳密な pullback を宇宙移送する。
規約：元の全 Hom と最初の辺と尾部・共有頂点を保持する。
使われ方：恒等高次単体の source 制限の自明 Kan 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => p.val.hom
local notation "Q" => q.val.hom
local notation "H" => cocartesianScaffoldSmallBridge n k
local notation "S" => cocartesianScaffoldLocalSource n k p q

/-- 同じ小さい同じ貼合せの元の native core は、同じ二脚の厳密な pullback。 -/
lemma cocartesianScaffoldStandardSource_isPullback :
    IsPullback
      (cocartesianPullbackNativeLiftPre P Q (ScaffoldBridgeOver.firstInclusion n H))
      (cocartesianPullbackNativeLiftPre P Q (ScaffoldBridgeOver.tailInclusion n H))
      (cocartesianPullbackNativeLiftPre P Q (ScaffoldBridgeOver.toFirst n H))
      (cocartesianPullbackNativeLiftPre P Q (ScaffoldBridgeOver.toTail n H)) :=
  ScaffoldBridgeOver.nativeLift_isPullback n H P Q

/-- 元の source pullback から同じ標準セルの source pullback への表示比較。 -/
def cocartesianScaffoldStandardSourcePullbackMap :
    pullback ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ⟶
      pullback (cocartesianPullbackNativeLiftPre P Q (ScaffoldBridgeOver.toFirst n H))
        (cocartesianPullbackNativeLiftPre P Q (ScaffoldBridgeOver.toTail n H)) :=
  spanPullbackMap _ _ _ _ (cocartesianScaffoldStandardSourceSharedMap n k p q)
    (cocartesianScaffoldStandardSourceFirstMap n k p q)
    (cocartesianScaffoldStandardSourceSecondMap n k p q)
    (cocartesianScaffoldStandardSourceFirstMap_naturality n k p q)
    (cocartesianScaffoldStandardSourceSecondMap_naturality n k p q)

/-- 三成分が同じ元の表示同型なので、source pullback の表示比較も同型。 -/
lemma cocartesianScaffoldStandardSourcePullbackMap_isIso :
    IsIso (cocartesianScaffoldStandardSourcePullbackMap n k p q) := by
  have : IsIso (cocartesianScaffoldStandardSourceSharedMap n k p q) :=
    cocartesianPullbackNativeLiftPre_isIso P Q
      (cocartesianScaffoldSmallSharedOverIso n k).hom
  have : IsIso (cocartesianScaffoldStandardSourceFirstMap n k p q) :=
    cocartesianPullbackNativeLiftPre_isIso P Q
      (cocartesianScaffoldSmallFirstOverIso n k).hom
  have : IsIso (cocartesianScaffoldStandardSourceSecondMap n k p q) :=
    cocartesianPullbackNativeLiftPre_isIso P Q
      (cocartesianScaffoldSmallTailOverIso n k).hom
  exact spanPullbackMap_isIso _ _ _ _ _ _ _ _ _

/-- 元の native core の同じホーン制限と、同じ厳密な pullback 表示の合成。 -/
def cocartesianScaffoldStandardBridgeSourceSegalMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      pullback (cocartesianPullbackNativeLiftPre P Q (ScaffoldBridgeOver.toFirst n H))
        (cocartesianPullbackNativeLiftPre P Q (ScaffoldBridgeOver.toTail n H)) :=
  cocartesianPullbackNativeLiftRestriction P Q (Over.mk H) ≫
    (cocartesianScaffoldStandardSource_isPullback n k p q).isoPullback.hom

end SerrePositivity.InfinityCategories
