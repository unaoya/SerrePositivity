module

public import SerrePositivity.InfinityCategories.F1.CocartesianGlobalNativeRestrictionTriangle
public import SerrePositivity.InfinityCategories.F1.CocartesianLocalNativeRestrictionGlobalEndpoints
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleDirectNaturality
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IsoEndpointNormalization

/-!
概要：元の全 Hom 上の既存の局所自然性自身は、端点表示だけをそろえて三角等式を満たす。
方針：元の指定値と同じ両端の回収から、既存の同型を同じ指定合成へ厳密に同定する。
規約：新しい局所自然性や大域自然性を選ばない。
使われ方：底上の局所自然性と元の大域分類作用の共有頂点での整合性。
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

/-- 両端の表示だけをそろえた、元の全 Hom 上の既存の指定局所自然性。 -/
def cocartesianLocalNativeRestrictionOriginalHomNormalizedIso :
    FunctorIso (cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap
      (cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).sourceMap :=
  F2.isoNormalizeEndpoints
    ((cocartesianLocalHomComparison_nativeRestrictionIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q))
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
      (cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_endpoints l k p q).1)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
      (cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_endpoints l k p q).2)

/-- 端点表示だけをそろえた既存の局所自然性は、同じ指定二因子の合成に厳密に一致。 -/
lemma cocartesianLocalNativeRestrictionOriginalHomNormalizedIso_eq :
    cocartesianLocalNativeRestrictionOriginalHomNormalizedIso l k p q =
    cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q := by
  exact F2.isoNormalizeEndpoints_eq_of_heq
    ((cocartesianLocalHomComparison_nativeRestrictionIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q))
    (cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
      (cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_endpoints l k p q).1)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
      (cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_endpoints l k p q).2)
    (cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_heq l k p q)

/-- 元の既存の局所自然性自身に対する、大域自然性の指定三角等式。 -/
def CocartesianOriginalNativeRestrictionTriangleCommutes : Prop :=
  IsoTriangleCommutes (cocartesianLocalNativeRestrictionOriginalHomNormalizedIso l k p q)
    ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q))
    (cocartesianBaseChangeGlobalTransportDirectIso l k p q)

/-- 同じ元の全 Hom 上で、既存の局所自然性自身の三角等式を回収する。 -/
lemma cocartesianOriginalNativeRestrictionTriangleCommutes :
    CocartesianOriginalNativeRestrictionTriangleCommutes l k p q := by
  exact IsoTriangleCommutes.replace_first
    (cocartesianGlobalNativeRestrictionTriangleCommutes l k p q)
    (cocartesianLocalNativeRestrictionOriginalHomNormalizedIso l k p q)
    (heq_of_eq (cocartesianLocalNativeRestrictionOriginalHomNormalizedIso_eq l k p q))

/-- 同じ三角形の直接辺も、元の直接の大域自然性に同じ表示正規化をした指定値。 -/
lemma cocartesianGlobalTransportDirectIso_originalNaturality_heq :
    HEq (cocartesianBaseChangeGlobalTransportDirectIso l k p q)
      ((cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q).postcomp
        (cocartesianBaseChangeHomCompositionNormalization l k p q)) := by
  exact HEq.trans (F2.functorIsoOfEq_heq _ _ _)
    (cocartesianBaseChangeTransportTriangleDirectIso_naturality_heq l k p q)

end SerrePositivity.InfinityCategories
