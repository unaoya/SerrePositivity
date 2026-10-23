module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeHomRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportNativeHomFactor
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondTriangleHomTransport
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomSpanSectionFactorCoherence

/-!
概要：第二面の結合因子と全局所 Hom の結合因子は、元の全 Hom 上で同じ span 比較になる。
方針：同じ指定切断の因子比較の前合成則と元の結合 Hom 比較の厳密な回収を使う。
規約：既存の指定比較の値を保持する。
使われ方：局所結合輸送と元の大域三角形の結合因子を同定する。
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

/-- 第二面の元の結合因子は、元の全 Hom 上で同じ結合 span の因子比較そのもの。 -/
lemma cocartesianBaseChangeSecondTriangleHomAssociativityTransportIso_factor_heq :
    HEq ((cocartesianBaseChangeSecondTriangleHomAssociativityTransportIso l k p q).precomp
      (cocartesianBaseChangeSecondTriangleHomComparison l k p q))
      (homSpanSectionTransportFactorIso
        (cocartesianBaseChangeAssociativityHomSpanOne l k p q)
        (cocartesianBaseChangeAssociativityHomSpanZero l k p q)
        (cocartesianBaseChangeAssociativityHomSpanOneSection l k p q)
        (cocartesianBaseChangeAssociativityHomSpanOne_isFullyFaithful l k p q)
        (cocartesianBaseChangeAssociativityHomSpanOneSection_projection l k p q)
        (cocartesianBaseChangeAssociativityHomComparison l k p q)) := by
  exact homSpanSectionTransportFactorIso_precomp_heq
    (cocartesianBaseChangeAssociativityHomSpanOne l k p q)
    (cocartesianBaseChangeAssociativityHomSpanZero l k p q)
    (cocartesianBaseChangeAssociativityHomSpanOneSection l k p q)
    (cocartesianBaseChangeAssociativityHomSpanOne_isFullyFaithful l k p q)
    (cocartesianBaseChangeAssociativityHomSpanOneSection_projection l k p q)
    (cocartesianBaseChangeSecondTriangleHomSecond l k p q)
    (cocartesianBaseChangeSecondTriangleHomComparison l k p q)
    (cocartesianBaseChangeAssociativityHomComparison l k p q)
    (cocartesianBaseChangeSecondTriangleHomComparison_second l k p q)

/-- 元の二重底変換で局所因子を引き戻すと、同じ大域結合 span の因子比較になる。 -/
lemma cocartesianIsoTransportNativeHomFactorIso_baseChange_heq :
    HEq ((cocartesianIsoTransportNativeHomFactorIso l k p q).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianBaseChangeNativeCoreEnriched l k).map p q)))
      (homSpanSectionTransportFactorIso
        (cocartesianBaseChangeAssociativityHomSpanOne l k p q)
        (cocartesianBaseChangeAssociativityHomSpanZero l k p q)
        (cocartesianBaseChangeAssociativityHomSpanOneSection l k p q)
        (cocartesianBaseChangeAssociativityHomSpanOne_isFullyFaithful l k p q)
        (cocartesianBaseChangeAssociativityHomSpanOneSection_projection l k p q)
        (cocartesianBaseChangeAssociativityHomComparison l k p q)) := by
  exact homSpanSectionTransportFactorIso_precomp_heq
    (cocartesianBaseChangeAssociativityHomSpanOne l k p q)
    (cocartesianBaseChangeAssociativityHomSpanZero l k p q)
    (cocartesianBaseChangeAssociativityHomSpanOneSection l k p q)
    (cocartesianBaseChangeAssociativityHomSpanOne_isFullyFaithful l k p q)
    (cocartesianBaseChangeAssociativityHomSpanOneSection_projection l k p q)
    (cocartesianIsoTransportNativeHomComparison l k p q)
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianBaseChangeNativeCoreEnriched l k).map p q))
    (cocartesianBaseChangeAssociativityHomComparison l k p q)
    (cocartesianIsoTransportNativeHomComparison_baseChange l k p q)

end SerrePositivity.InfinityCategories
