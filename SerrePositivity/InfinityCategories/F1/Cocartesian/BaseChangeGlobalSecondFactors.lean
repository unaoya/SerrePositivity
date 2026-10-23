module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleSecondNaturality

/-!
概要：元の全 Hom 上の指定結合輸送と二回目の大域自然性の因子を名前で束ねる。
方針：既存の二つの指定同型に同じ元の作用を前後合成する。
規約：元の指定値を選び直さない。
使われ方：第二辺の合成を保って局所自然性の三角等式を回収する。
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

/-- 元の全 Hom 上の指定結合輸送の因子。 -/
def cocartesianBaseChangeGlobalNativeTransportFactorIso :=
  ((cocartesianBaseChangeNativeHomTransportIso l k p q).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))).postcomp
            (cocartesianBaseChangeHomTransport l
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))

/-- 元の全 Hom 上の二回目の大域自然性の因子。 -/
def cocartesianBaseChangeGlobalSecondNaturalityFactorIso :=
  (cocartesianBaseChangeHomNaturalityIso l
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q))

end SerrePositivity.InfinityCategories
