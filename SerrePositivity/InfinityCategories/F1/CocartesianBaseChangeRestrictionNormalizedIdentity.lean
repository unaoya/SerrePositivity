module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeFirstRestrictionFactor
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleFirstNaturality

/-!
概要：元の第一辺の制限正方形は、元の全 Hom 上の正規化した指定因子比較で可換。
方針：厳密な span の同じ制限・指定切断・全 Hom 作用に一般の正規化則を適用する。
規約：既存の制限自然性と元の第一辺の指定同型を保持する。
使われ方：三辺の指定比較を元の大域自然性と局所自然性の同じ貼り合わせへ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全 Hom 上で、制限自然性と第一辺の正規化した因子比較は元の源の因子比較。 -/
lemma cocartesianBaseChangeHomTransport_restrictionIso_normalized_identity
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HomSpanSectionRestrictionCommutesAt
    (cocartesianBaseChangeHomSpanZero k p q) (cocartesianBaseChangeHomSpanOne k p q)
    (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeRestrictedHomMap l k p q)
    (cocartesianBaseChangeHomSpanOneSection k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q)
    (cocartesianBaseChangeHomRestrictionZero l k p q)
    (cocartesianBaseChangeHomRestrictionOne l k p q)
    (cocartesianBaseChangeHomSpanOne_isQCatEquivalence k p q)
    (cocartesianBaseChangeRestrictedHomSpanOne_isFullyFaithful l k p q)
    (cocartesianBaseChangeHomSpanOneSection_projection k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q)
    (cocartesianBaseChangeRestrictedHomMap_zero l k p q)
    (cocartesianBaseChangeRestrictedHomMap_one l k p q)
    (cocartesianBaseChangeHomComparison k p q)
    (cocartesianBaseChangeRestrictedGlobalFactor_source l k p q)
    (cocartesianBaseChangeRestrictedGlobalFactor_target l k p q) := by
  exact homSpanSectionTransportNaturalityIso_normalized_identity
    (cocartesianBaseChangeHomSpanZero k p q) (cocartesianBaseChangeHomSpanOne k p q)
    (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeRestrictedHomMap l k p q)
    (cocartesianBaseChangeHomSpanOneSection k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q)
    (cocartesianBaseChangeHomRestrictionZero l k p q)
    (cocartesianBaseChangeHomRestrictionOne l k p q)
    (cocartesianBaseChangeHomSpanOne_isQCatEquivalence k p q)
    (cocartesianBaseChangeRestrictedHomSpanOne_isFullyFaithful l k p q)
    (cocartesianBaseChangeHomSpanOneSection_projection k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q)
    (cocartesianBaseChangeRestrictedHomMap_zero l k p q)
    (cocartesianBaseChangeRestrictedHomMap_one l k p q)
    (cocartesianBaseChangeHomComparison k p q)
    (cocartesianBaseChangeRestrictedGlobalFactor_source l k p q)
    (cocartesianBaseChangeRestrictedGlobalFactor_target l k p q)

/-- 正規化した制限因子は、元の大域 Hom 上の同じ三角形の第一辺を保持する。 -/
lemma cocartesianBaseChangeRestrictedGlobalNormalizedFactorIso_first_heq
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HEq (cocartesianBaseChangeRestrictedGlobalNormalizedFactorIso l k p q)
      ((cocartesianBaseChangeTriangleHomFirst_restrictedTransportIso l k p q).precomp
        (cocartesianBaseChangeTriangleHomComparison l k p q)) := by
  exact HEq.trans
    (cocartesianBaseChangeRestrictedGlobalNormalizedFactorIso_heq l k p q)
    (cocartesianBaseChangeTriangleHomFirst_transportIso_naturality_heq l k p q).symm

end SerrePositivity.InfinityCategories
