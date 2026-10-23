module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeGlobalTransportTriangle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeFirstGlobalFactorDecomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoLocalTriangleIdentity

/-!
概要：元の全 Hom 上で、指定局所比較の三辺の貼り合わせは直接の指定大域自然性に一致。
方針：元の輸送三角形と第一辺の制限正方形を、同じ指定因子で消去する。
規約：元の全 Hom・指定結合輸送・底制限自然性・大域自然性を保持する。
使われ方：指定局所自然性と元の大域分類作用の共有頂点における整合性。
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

/-- 元の輸送三角形と同じ指定因子から得る、局所比較の三角等式。 -/
def CocartesianBaseChangeGlobalLocalTriangleCommutes : Prop :=
  FunctorIsoLocalTriangleCommutes
    ((cocartesianBaseChangeGlobalTransportCompositionIso l k p q).symm ≪≫
      (cocartesianBaseChangeGlobalNativeTransportFactorIso l k p q).postcomp
        (cocartesianBaseChangeRestrictedHomTransport l k p q))
    ((cocartesianBaseChangeGlobalSecondNaturalityFactorIso l k p q).postcomp
      (cocartesianBaseChangeRestrictedHomTransport l k p q) ≪≫
        (cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).symm)
    ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q))
    (cocartesianBaseChangeGlobalTransportDirectIso l k p q)

/-- 元の全 Hom 上で、指定された局所比較の三角形は同じ直接の大域自然性と整合する。 -/
lemma cocartesianBaseChangeGlobalLocalTriangleCommutes :
    CocartesianBaseChangeGlobalLocalTriangleCommutes l k p q := by
  exact functorIsoLocalTriangle_of_postcomp_and_source_pasting
    (cocartesianBaseChangeRestrictedHomTransport l k p q)
    (cocartesianBaseChangeGlobalNativeTransportFactorIso l k p q)
    (cocartesianBaseChangeGlobalSecondNaturalityFactorIso l k p q)
    (cocartesianBaseChangeGlobalTransportCompositionIso l k p q)
    (cocartesianBaseChangeGlobalTransportDirectIso l k p q)
    (cocartesianBaseChangeFirstGlobalRestrictionIso l k p q)
    (cocartesianBaseChangeFirstGlobalFactorIso l k p q)
    ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q))
    (cocartesianBaseChangeFirstGlobalRestriction_source l k p q)
    (cocartesianBaseChangeGlobalTransportTriangleCommutes l k p q)
    (cocartesianBaseChangeFirstGlobalPasting_normalized l k p q)

end SerrePositivity.InfinityCategories
