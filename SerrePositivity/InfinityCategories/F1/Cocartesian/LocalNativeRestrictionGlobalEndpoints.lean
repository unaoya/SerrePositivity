module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalNativeRestrictionGlobalCoherence

/-!
概要：既存の局所自然性全体を元の全 Hom に戻した両端は、同じ大域三角形の両端。
方針：元の指定合成の始点正規化と前合成を、既存の端点回収へ適用する。
規約：元の全 Hom と既存の指定局所自然性を保持する。
使われ方：同じ元の局所自然性自身に、大域自然性の三角等式を移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 既存の局所自然性を元の全 Hom に戻した両端は、回収した指定合成の同じ両端。 -/
lemma cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_endpoints
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    ((cocartesianLocalHomComparison_nativeRestrictionIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q)).sourceMap =
      (cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap ∧
    ((cocartesianLocalHomComparison_nativeRestrictionIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q)).targetMap =
      (cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).sourceMap := by
  have hs₀ := functorIso_precomp_sourceMap_recover
    (cocartesianLocalNativeRestrictionNativeFactorIso l k p q)
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianLocalNativeRestrictionNativeFactor_originalHom_endpoints l k p q).1
  have hs := functorIsoOfEq_precomp_sourceMap_of_eq
    (cocartesianLocalNativeRestrictionCompositeIso l k p q)
    (cocartesianLocalNativeRestrictionNativeFactor_source l k p q) rfl
    (cocartesianSingleBaseChangeHomAction k p q) hs₀
  have ht₀ := functorIso_precomp_targetMap_recover
    (cocartesianIteratedLocalHomComparison_restrictionIso l k p q)
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianIteratedLocalHomComparison_restrictionIso_originalHom_endpoints l k p q).2
  have ht := functorIsoOfEq_precomp_targetMap_of_eq
    (cocartesianLocalNativeRestrictionCompositeIso l k p q)
    (cocartesianLocalNativeRestrictionNativeFactor_source l k p q) rfl
    (cocartesianSingleBaseChangeHomAction k p q) ht₀
  exact ⟨hs, ht⟩

end SerrePositivity.InfinityCategories
