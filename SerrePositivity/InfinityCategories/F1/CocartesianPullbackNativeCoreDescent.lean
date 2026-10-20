module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackNativeCoreFamilies

/-!
概要：両射影を底変換した元の Hom の core の整合する族を、大域の元の Hom へ貼る。
方針：厳密な Hom 同型で局所 Hom の降下へ移し、同じ制限で各脚を回収する。
規約：元の全相対 Hom と任意のパラメーター単体集合を保持する。
使われ方：元の分類主写像の Hom 比較のセルによる降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {J : Type v} [Category.{w} J] [Small.{u} J]
  {T E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
  (D : J ⥤ Over B) (hc : IsColimit ((Over.forgetCocone B).whisker D))
  (s : ∀ j, T ⟶ (quasicategoryCore (cocartesianRelativeFunctorSpace
    (pullback.fst (D.obj j).hom p) (pullback.fst (D.obj j).hom q)) : SSet.{u}))
  (hs : ∀ {j k} (f : j ⟶ k), s j =
    s k ≫ quasicategoryCoreMap (cocartesianPullbackNativePre p q (D.map f)))

/-- 底を覆う各引き戻しの元の Hom の core の族を、大域の元の Hom の core へ貼る。 -/
def cocartesianPullbackNativeCoreColimitLift :
    T ⟶ (quasicategoryCore (cocartesianRelativeFunctorSpace p q) : SSet.{u}) :=
  cocartesianPullbackHomCoreColimitLift p q D hc
    (cocartesianPullbackNativeCoreFamily p q D s)
    (cocartesianPullbackNativeCoreFamily_compatible p q D s hs)

/-- 貼った同じ族は、両射影を底変換した元の Hom への各制限を厳密に回収する。 -/
lemma cocartesianPullbackNativeCoreColimitLift_fac (j : J) :
    cocartesianPullbackNativeCoreColimitLift p q D hc s hs ≫
      quasicategoryCoreMap (cocartesianPullbackNativeRestriction p q (D.obj j)) = s j := by
  apply (cancel_mono
    (quasicategoryCoreFunctor.mapIso (cocartesianPullbackHomIso p q (D.obj j))).hom).mp
  change (_ ≫ quasicategoryCoreFunctor.map _) ≫ quasicategoryCoreFunctor.map _ = _
  rw [Category.assoc, ← quasicategoryCoreFunctor.map_comp,
    cocartesianPullbackNativeRestriction_iso]
  exact cocartesianPullbackHomCoreColimitLift_fac p q D hc
    (cocartesianPullbackNativeCoreFamily p q D s)
    (cocartesianPullbackNativeCoreFamily_compatible p q D s hs) j

/-- 各引き戻しの元の Hom 上で同じ族を回収する大域の族は一意。 -/
lemma cocartesianPullbackNativeCoreColimitLift_unique
    (m : T ⟶ (quasicategoryCore (cocartesianRelativeFunctorSpace p q) : SSet.{u}))
    (hm : ∀ j, m ≫
      quasicategoryCoreMap (cocartesianPullbackNativeRestriction p q (D.obj j)) = s j) :
    m = cocartesianPullbackNativeCoreColimitLift p q D hc s hs := by
  apply cocartesianPullbackHomCoreColimitLift_unique p q D hc
    (cocartesianPullbackNativeCoreFamily p q D s)
    (cocartesianPullbackNativeCoreFamily_compatible p q D s hs) m
  intro j
  unfold cocartesianPullbackNativeCoreFamily
  rw [← hm j, Category.assoc]
  change m ≫ quasicategoryCoreFunctor.map _ =
    m ≫ quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _
  rw [← quasicategoryCoreFunctor.map_comp, cocartesianPullbackNativeRestriction_iso]

end SerrePositivity.InfinityCategories
