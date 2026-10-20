module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackRestrictionNaturality
public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackHomCoreDescent

/-!
概要：各底変換の元の cocartesian Hom の core の族を、同じ局所 Hom の族へ移す。
方針：厳密な Hom 同型に core 関手を適用し、元の前合成の自然性を保つ。
規約：同じ全パラメーターの族を使い、可変の底の充填性を要求しない。
使われ方：底を覆う余極限から元の Hom の core を回収する降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {J : Type v} [Category.{w} J]
  {T E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
  (D : J ⥤ Over B)
  (s : ∀ j, T ⟶ (quasicategoryCore (cocartesianRelativeFunctorSpace
    (pullback.fst (D.obj j).hom p) (pullback.fst (D.obj j).hom q)) : SSet.{u}))

/-- 各底変換の元の Hom の core の族を、同じ局所 Hom の core の族へ写す。 -/
def cocartesianPullbackNativeCoreFamily (j : J) :
    T ⟶ (quasicategoryCore (cocartesianPullbackHomSpace p q (D.obj j)) : SSet.{u}) :=
  s j ≫ quasicategoryCoreMap (cocartesianPullbackHomIso p q (D.obj j)).hom

/-- 元の Hom の族の整合性は、同じ局所 Hom の族の厳密な整合性を与える。 -/
lemma cocartesianPullbackNativeCoreFamily_compatible
    (hs : ∀ {j k} (f : j ⟶ k), s j =
      s k ≫ quasicategoryCoreMap (cocartesianPullbackNativePre p q (D.map f)))
    {j k : J} (f : j ⟶ k) :
    cocartesianPullbackNativeCoreFamily p q D s j =
      cocartesianPullbackNativeCoreFamily p q D s k ≫
        quasicategoryCoreMap (cocartesianPullbackHomPre p q (D.map f)) := by
  unfold cocartesianPullbackNativeCoreFamily
  rw [hs f, Category.assoc]
  change s k ≫ quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _ =
    (s k ≫ quasicategoryCoreFunctor.map _) ≫ quasicategoryCoreFunctor.map _
  rw [← quasicategoryCoreFunctor.map_comp, cocartesianPullbackNativePre_iso,
    quasicategoryCoreFunctor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories
