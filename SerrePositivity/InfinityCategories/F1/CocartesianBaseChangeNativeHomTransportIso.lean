module

public import SerrePositivity.InfinityCategories.F1.CocartesianIsoTransportNativeHomMap
public import SerrePositivity.InfinityCategories.F1.CocartesianIsoTransportNativeHomTransport

/-!
概要：既存の指定結合同型の Hom 共役と、既存の結合 Hom 輸送を同じ分類作用で結ぶ。
方針：raw 共役の core と元の core 共役の厳密な一致を既存の比較へ代入する。
規約：元の全局所 Hom・分類写像・結合輸送を保持する。
使われ方：二重局所比較と直接の局所比較の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の指定 Hom 結合同型の分類像は、既存の結合輸送によって元の局所分類作用へ戻る。 -/
def cocartesianBaseChangeNativeHomTransportIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      (((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
        cocartesianStraighteningHomInterval
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q)) ≫
        cocartesianBaseChangeAssociativityHomTransport l k p q)
      (cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) :=
  F2.functorIsoOfEq (cocartesianIsoTransportNativeHomTransportIso l k p q)
    (by rw [cocartesianIsoTransportNativeHomMap_eq]) rfl

end SerrePositivity.InfinityCategories
