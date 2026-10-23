module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalNativeRestrictionGlobalPasting
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.IsoPastingEndpointTransport

/-!
概要：既存の nativeRestrictionIso を元の全 Hom に戻すと、同じ指定二因子の合成になる。
方針：同じ一回目の底変換・三端点・指定値を保持して元の貼り合わせを回収する。
規約：既存の局所自然性全体と元の全 Hom 作用を保持する。
使われ方：元の三辺の等式を既存の局所自然性の指定値へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 既存の局所自然性全体の前合成は、元の全 Hom 上の同じ指定二因子の合成に一致。 -/
lemma cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_heq
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HEq ((cocartesianLocalHomComparison_nativeRestrictionIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q))
      (cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q) := by
  have h₁ := functorIsoOfEq_precomp_heq
    (cocartesianLocalNativeRestrictionCompositeIso l k p q)
    (cocartesianLocalNativeRestrictionNativeFactor_source l k p q) rfl
    (cocartesianSingleBaseChangeHomAction k p q)
  have hs := congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
    (cocartesianLocalNativeRestrictionNativeFactor_originalHom_endpoints l k p q).1
  have hm := congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
    (cocartesianLocalNativeRestrictionNativeFactor_originalHom_endpoints l k p q).2
  have ht := congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
    (cocartesianIteratedLocalHomComparison_restrictionIso_originalHom_endpoints l k p q).2
  have hp := F2.functorIso_precomp_trans
    (cocartesianLocalNativeRestrictionNativeFactorIso l k p q)
    (cocartesianIteratedLocalHomComparison_restrictionIso l k p q)
    (cocartesianSingleBaseChangeHomAction k p q)
  have hv := iso_pasting_heq_of_endpoint_eq
    ((cocartesianLocalNativeRestrictionNativeFactorIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q))
    ((cocartesianIteratedLocalHomComparison_restrictionIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q))
    (cocartesianBaseChangeGlobalNativeComparisonIso l k p q)
    (cocartesianBaseChangeGlobalRestrictionComparisonNormalizedIso l k p q)
    hs hm ht
    (cocartesianLocalNativeRestrictionNativeFactor_originalHom_heq l k p q)
    (cocartesianBaseChangeGlobalRestrictionComparisonNormalizedIso_originalHom_heq l k p q)
  exact HEq.trans h₁ (HEq.trans (heq_of_eq hp) hv)

end SerrePositivity.InfinityCategories
