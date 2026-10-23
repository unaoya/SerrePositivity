module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeCorePushout
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeLiftRestriction
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramPushout
public import SerrePositivity.InfinityCategories.F1.Universe.Pushouts
public import SerrePositivity.InfinityCategories.F1.Universe.RelativeOverPre

/-!
概要：任意のセル貼合せで、同じ source と分類先の Hom は厳密な pullback をなす。
方針：単射な境界包含を持つ側を入れ替え、同じ四射の貼合せに一般補題を適用する。
規約：境界から既存部分への貼付け写像の単射性を要求しない。
使われ方：有限セルと骨格の降下で元の全 Hom の延長を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {B : SSet.{u}} {a b c d : Over B}
  (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
  (hp : IsPushout f.left g.left i.left j.left)

include hp

/-- 任意の貼付け写像によるセル付加を、元の native core の同じ pullback へ移す。 -/
lemma cocartesianCellAttachment_nativeLift_isPullback
    {E F : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
    [Mono f.left] :
    IsPullback (cocartesianPullbackNativeLiftPre p q i)
      (cocartesianPullbackNativeLiftPre p q j)
      (cocartesianPullbackNativeLiftPre p q f)
      (cocartesianPullbackNativeLiftPre p q g) :=
  (core_cocartesianPullbackNativePre_isPullback_of_isPushout p q g f j i hp.flip).map
    (SSet.uliftFunctor.{u + 1, u})

/-- 同じセル貼合せで、分類先の同じ両端固定 Hom も同じ宇宙の pullback をなす。 -/
lemma cocartesianCellAttachment_interval_isPullback
    {X : SSet.{u + 1}} (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X) :
    IsPullback (intervalDiagramOverPre P Q (uliftOverMorphism i))
      (intervalDiagramOverPre P Q (uliftOverMorphism j))
      (intervalDiagramOverPre P Q (uliftOverMorphism f))
      (intervalDiagramOverPre P Q (uliftOverMorphism g)) :=
  (intervalDiagramOverPre_isPullback_of_isPushout P Q
    (uliftOverMorphism f) (uliftOverMorphism g) (uliftOverMorphism i) (uliftOverMorphism j)
    (uliftSSet_isPushout hp)).flip

end SerrePositivity.InfinityCategories
