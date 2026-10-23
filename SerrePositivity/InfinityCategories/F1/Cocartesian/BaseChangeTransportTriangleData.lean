module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomZeroNormalization
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomRestrictedTransport
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondHomCompositeTransport
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomTransport
public import SerrePositivity.InfinityCategories.F1.HomTransportTriangleIdentity

/-!
概要：元の直接の底変換 Hom 輸送は、元の二回の比較と結合比較の輸送の合成と同型。
方針：元の同じ比較三角形の共通 Hom 上で三辺を比較し、同値な終点評価で降ろす。
規約：既存の cocartesianBaseChangeHomTransport と元の全高次の比較を保持する。
使われ方：元の分類 Hom 作用の二次元 Segal 制限と底制限の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 比較三角形の二回目の輸送に指定された同型。 -/
def cocartesianBaseChangeTransportTriangleSecondIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      ((cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q) ≫ (cocartesianBaseChangeAssociativityHomTransport l k p q ≫
          cocartesianBaseChangeHomTransport l
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))
      (cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanOne l k p q) :=
  F2.functorIsoOfEq
    (FunctorIso.precomp (cocartesianBaseChangeSecondHomCompositeTransportIso l k p q)
      (cocartesianBaseChangeTriangleHomSecond l k p q))
    (by rw [← Category.assoc, ← cocartesianBaseChangeTriangleHom_second_one l k p q])
    (cocartesianBaseChangeTriangleHom_middle l k p q).symm

/-- 比較三角形の直接の輸送に指定された同型。 -/
def cocartesianBaseChangeTransportTriangleDirectIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      ((cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q) ≫ (cocartesianBaseChangeHomTransport (l ⋙ k) p q ≫
        cocartesianBaseChangeHomCompositionNormalization l k p q))
      (cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanZero l k p q) :=
  F2.functorIsoOfEq
    ((cocartesianBaseChangeTriangleHomLong_transportIso l k p q).postcomp
      (cocartesianBaseChangeHomCompositionNormalization l k p q))
    (Category.assoc _ _ _)
    (cocartesianBaseChangeTriangleHom_zero_normalization l k p q)

end SerrePositivity.InfinityCategories
