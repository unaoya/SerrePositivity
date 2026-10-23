module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeGlobalCompositionNative
public import SerrePositivity.InfinityCategories.F1.FunctorIsoWhiskeredPasting

/-!
概要：元の全 Hom 上の指定結合輸送の因子は、既存の局所結合比較の第二因子を回収する。
方針：同じ二重底変換による前合成と二回の後合成を交換する。
規約：既存の指定結合輸送と始点の正規化を保持する。
使われ方：既存の局所結合比較の前合成と三辺の第一因子の同定。
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

/-- 元の全 Hom 上の指定結合輸送を、同じ底でさらに輸送した因子。 -/
def cocartesianBaseChangeGlobalNativeTransportPostIso :=
  (cocartesianBaseChangeGlobalNativeTransportFactorIso l k p q).postcomp
    (cocartesianBaseChangeRestrictedHomTransport l k p q)

/-- 同じ第二因子の前合成は、指定された大域因子と同じ終点作用を回収する。 -/
lemma cocartesianBaseChangeGlobalNativeTransport_native_target :
    ((cocartesianIteratedLocalNativeNormalizedTransportFactorIso l k p q).precomp
      (cocartesianDoubleBaseChangeHomAction l k p q)).targetMap =
    (cocartesianBaseChangeGlobalNativeTransportPostIso l k p q).targetMap := by
  exact functorIso_normalized_postcomp_precomp_twice_target
    (cocartesianBaseChangeNativeHomTransportIso l k p q)
    (cocartesianDoubleBaseChangeHomAction l k p q)
    (cocartesianBaseChangeHomTransport l
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianBaseChangeRestrictedHomTransport l k p q)
    (cocartesianIteratedLocalNativeTransportFactor_source l k p q)

/-- 同じ二回の後合成と前合成は、既存の第二因子の指定値を回収する。 -/
lemma cocartesianBaseChangeGlobalNativeTransport_native_heq :
    HEq (cocartesianBaseChangeGlobalNativeTransportPostIso l k p q)
      ((cocartesianIteratedLocalNativeNormalizedTransportFactorIso l k p q).precomp
        (cocartesianDoubleBaseChangeHomAction l k p q)) := by
  exact functorIso_normalized_postcomp_precomp_twice_heq
    (cocartesianBaseChangeNativeHomTransportIso l k p q)
    (cocartesianDoubleBaseChangeHomAction l k p q)
    (cocartesianBaseChangeHomTransport l
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianBaseChangeRestrictedHomTransport l k p q)
    (cocartesianIteratedLocalNativeTransportFactor_source l k p q)

end SerrePositivity.InfinityCategories
