module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalHomOverNaturalityCoherence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalNativeRestrictionGlobalEndpoints

/-!
概要：元の全 Hom 上の底上の自然性の像は、同じ大域三角形の両端を回収する。
方針：充満忠実な逆像の像の端点を、既存の native 自然性の端点へ結ぶ。
規約：指定された元の同型と全 Hom 作用を保持する。
使われ方：同じ over 自然性の像への三角等式の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の全 Hom 上の同じ底上の自然性を、同じ端点正規化へ写した指定同型。 -/
def cocartesianLocalHomOverNaturalityOriginalHomImageIso :=
  ((cocartesianLocalHomComparison_overNaturalityIso l k p q).precomp
    (cocartesianSingleBaseChangeHomAction k p q)).postcomp
    (cocartesianBaseChangeHomCompositionNormalization l k p q)

/-- 同じ指定像の両端は元の大域三角形の両端そのもの。 -/
lemma cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints :
    (cocartesianLocalHomOverNaturalityOriginalHomImageIso l k p q).sourceMap =
      (cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap ∧
    (cocartesianLocalHomOverNaturalityOriginalHomImageIso l k p q).targetMap =
      (cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).sourceMap := by
  have h := (cocartesianLocalHomOverNormalization_isFullyFaithful l k p q).preimageNormalizedFunctorIso_precomp_postcomp_endpoints
      (cocartesianLocalHomOverNaturalitySource l k p q)
      (cocartesianLocalHomOverNaturalityTarget l k p q)
      (cocartesianLocalHomComparison_nativeRestrictionIso l k p q) rfl
      (cocartesianLocalHomOverNaturalityTarget_normalization l k p q)
      (cocartesianSingleBaseChangeHomAction k p q)
  have hs := functorIso_precomp_sourceMap_recover
    (cocartesianLocalHomComparison_nativeRestrictionIso l k p q)
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_endpoints l k p q).1
  have ht := functorIso_precomp_targetMap_recover
    (cocartesianLocalHomComparison_nativeRestrictionIso l k p q)
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_endpoints l k p q).2
  exact ⟨h.1.trans hs, h.2.trans ht⟩

end SerrePositivity.InfinityCategories
