module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleHomZeroNormalization
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleHomRestrictedTransport
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondHomCompositeTransport
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleHomTransport
public import SerrePositivity.InfinityCategories.F1.HomTransportTriangleCoherence

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

/-- 元の直接の輸送を、元の結合比較・二回目の比較・最初の比較の底制限の合成で回収する。 -/
def cocartesianBaseChangeHomTransport_compositionIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      ((cocartesianBaseChangeAssociativityHomTransport l k p q ≫
          cocartesianBaseChangeHomTransport l
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫
        cocartesianBaseChangeRestrictedHomTransport l k p q)
      (cocartesianBaseChangeHomTransport (l ⋙ k) p q ≫
        cocartesianBaseChangeHomCompositionNormalization l k p q) := by
  apply homTransportTriangleCoherence
    (cocartesianBaseChangeTriangleHomFirst l k p q ≫
      cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeTriangleHomFirst l k p q ≫
      cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeTriangleHomLong l k p q ≫
      cocartesianBaseChangeHomSpanOne (l ⋙ k) p q)
  · exact cocartesianBaseChangeTriangleHomLong_one_isQCatEquivalence l k p q
  · exact cocartesianBaseChangeTriangleHomFirst_restrictedTransportIso l k p q
  · have e := FunctorIso.precomp (cocartesianBaseChangeSecondHomCompositeTransportIso l k p q)
      (cocartesianBaseChangeTriangleHomSecond l k p q)
    simp only [← Category.assoc] at e
    rw [← cocartesianBaseChangeTriangleHom_second_one l k p q,
      ← cocartesianBaseChangeTriangleHom_middle l k p q] at e
    simpa only [Category.assoc] using e
  · have e := (cocartesianBaseChangeTriangleHomLong_transportIso l k p q).postcomp
      (cocartesianBaseChangeHomCompositionNormalization l k p q)
    rw [cocartesianBaseChangeTriangleHom_zero_normalization l k p q] at e
    simpa only [Category.assoc] using e

end SerrePositivity.InfinityCategories
