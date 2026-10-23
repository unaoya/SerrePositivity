module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexStandardSourceComponents
public import SerrePositivity.InfinityCategories.F1.Joins.SpanPullbackIsomorphism
public import SerrePositivity.InfinityCategories.F1.Simplicial.InnerTwoHornHomPullbacks
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePullbacks

/-!
概要：元の source pullback と同じ小さい標準内ホーンの native core pullback を同型で結ぶ。
方針：同じ三つの表示同型を作用させ、元の core の厳密な pullback を宇宙移送する。
規約：元の全 Hom と二辺・共有頂点を保持する。
使われ方：恒等二単体の source 制限の自明 Kan 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => p.val.hom
local notation "Q" => q.val.hom
local notation "H" => cocartesianTwoSimplexSmallStandardHorn k
local notation "S" => cocartesianTwoSimplexLocalSource k p q

/-- 同じ小さい標準内ホーンの元の native core は、同じ二脚の厳密な pullback。 -/
lemma cocartesianTwoSimplexStandardSource_isPullback :
    IsPullback
      (cocartesianPullbackNativeLiftPre P Q (InnerTwoHornOver.firstInclusion H))
      (cocartesianPullbackNativeLiftPre P Q (InnerTwoHornOver.secondInclusion H))
      (cocartesianPullbackNativeLiftPre P Q (InnerTwoHornOver.toFirst H))
      (cocartesianPullbackNativeLiftPre P Q (InnerTwoHornOver.toSecond H)) :=
  (InnerTwoHornOver.nativeCore_isPullback P Q H).flip.map (SSet.uliftFunctor.{u + 1, u})

/-- 元の source pullback から同じ標準セルの source pullback への表示比較。 -/
def cocartesianTwoSimplexStandardSourcePullbackMap :
    pullback ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ⟶
      pullback (cocartesianPullbackNativeLiftPre P Q (InnerTwoHornOver.toFirst H))
        (cocartesianPullbackNativeLiftPre P Q (InnerTwoHornOver.toSecond H)) :=
  spanPullbackMap _ _ _ _ (cocartesianTwoSimplexStandardSourceSharedMap k p q)
    (cocartesianTwoSimplexStandardSourceFirstMap k p q)
    (cocartesianTwoSimplexStandardSourceSecondMap k p q)
    (cocartesianTwoSimplexStandardSourceFirstMap_naturality k p q)
    (cocartesianTwoSimplexStandardSourceSecondMap_naturality k p q)

/-- 三成分が同じ元の表示同型なので、source pullback の表示比較も同型。 -/
lemma cocartesianTwoSimplexStandardSourcePullbackMap_isIso :
    IsIso (cocartesianTwoSimplexStandardSourcePullbackMap k p q) := by
  have : IsIso (cocartesianTwoSimplexStandardSourceSharedMap k p q) :=
    cocartesianPullbackNativeLiftPre_isIso P Q
      (cocartesianTwoSimplexSmallStandardSharedOverIso k).hom
  have : IsIso (cocartesianTwoSimplexStandardSourceFirstMap k p q) :=
    cocartesianPullbackNativeLiftPre_isIso P Q
      (cocartesianTwoSimplexSmallStandardFirstOverIso k).hom
  have : IsIso (cocartesianTwoSimplexStandardSourceSecondMap k p q) :=
    cocartesianPullbackNativeLiftPre_isIso P Q
      (cocartesianTwoSimplexSmallStandardSecondOverIso k).hom
  exact spanPullbackMap_isIso _ _ _ _ _ _ _ _ _

/-- 元の native core の同じホーン制限と、同じ厳密な pullback 表示の合成。 -/
def cocartesianTwoSimplexStandardHornSourceSegalMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      pullback (cocartesianPullbackNativeLiftPre P Q (InnerTwoHornOver.toFirst H))
        (cocartesianPullbackNativeLiftPre P Q (InnerTwoHornOver.toSecond H)) :=
  cocartesianPullbackNativeLiftRestriction P Q (Over.mk H) ≫
    (cocartesianTwoSimplexStandardSource_isPullback k p q).isoPullback.hom

end SerrePositivity.InfinityCategories
