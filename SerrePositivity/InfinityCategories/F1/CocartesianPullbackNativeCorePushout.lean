module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackHomPushout
public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackNativeFunctor

/-!
概要：両射影を底変換した元の cocartesian Hom の core を、底の pushout 上で貼る。
方針：同じ局所 Hom の pullback を、元の Hom との自然な厳密同型で移す。
規約：全射影は元の底変換の Hom の制限そのもの。
使われ方：同じ分類 Hom 作用の区間と高次セルの貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 元の底変換の Hom の同型は、core の制限とも厳密に可換。 -/
lemma core_cocartesianPullbackNativePre_iso {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
    {a b : Over B} (f : a ⟶ b) :
    quasicategoryCoreMap (cocartesianPullbackNativePre p q f) ≫
        quasicategoryCoreMap (cocartesianPullbackHomIso p q a).hom =
      quasicategoryCoreMap (cocartesianPullbackHomIso p q b).hom ≫
        quasicategoryCoreMap (cocartesianPullbackHomPre p q f) := by
  change quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _ =
    quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _
  rw [← Functor.map_comp, ← Functor.map_comp, cocartesianPullbackNativePre_iso]

/-- 底の pushout は、両射影を底変換した元の Hom の core の厳密な pullback を与える。 -/
lemma core_cocartesianPullbackNativePre_isPullback_of_isPushout
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
    {a b c d : Over B} (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
    [Mono g.left] (hp : IsPushout f.left g.left i.left j.left) :
    IsPullback (quasicategoryCoreMap (cocartesianPullbackNativePre p q j))
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q i))
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q g))
      (quasicategoryCoreMap (cocartesianPullbackNativePre p q f)) := by
  apply (core_cocartesianPullbackHomPre_isPullback_of_isPushout p q f g i j hp).of_iso'
    (quasicategoryCoreFunctor.mapIso (cocartesianPullbackHomIso p q d))
    (quasicategoryCoreFunctor.mapIso (cocartesianPullbackHomIso p q c))
    (quasicategoryCoreFunctor.mapIso (cocartesianPullbackHomIso p q b))
    (quasicategoryCoreFunctor.mapIso (cocartesianPullbackHomIso p q a))
  · exact (core_cocartesianPullbackNativePre_iso p q j).symm
  · exact (core_cocartesianPullbackNativePre_iso p q i).symm
  · exact (core_cocartesianPullbackNativePre_iso p q g).symm
  · exact (core_cocartesianPullbackNativePre_iso p q f).symm

end SerrePositivity.InfinityCategories
