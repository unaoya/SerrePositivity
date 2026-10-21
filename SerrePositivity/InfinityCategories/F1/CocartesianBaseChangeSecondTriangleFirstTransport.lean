module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleHomFirst
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomTransport
public import SerrePositivity.InfinityCategories.F1.HomSpanSectionTransport

/-!
概要：元の分解三角形の最初の面での二回目の底変換の指定輸送比較。
方針：元の二回目の比較 span の指定切断の因子比較を使う。
規約：既存の合成比較の中の同じ指定同型を保持する。
使われ方：第二面の同型を二回目の底変換自然性へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 分解三角形の同じ最初の面で、二回目の輸送が元の両評価を結ぶ指定比較。 -/
def cocartesianBaseChangeSecondTriangleHomFirstTransportIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      ((cocartesianBaseChangeSecondTriangleHomFirst l k p q ≫
        cocartesianBaseChangeHomSpanOne l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫
        cocartesianBaseChangeHomTransport l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
      (cocartesianBaseChangeSecondTriangleHomFirst l k p q ≫
        cocartesianBaseChangeHomSpanZero l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne l
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration l _ _
  exact homSpanSectionTransportFactorIso
    (cocartesianBaseChangeHomSpanOne l _ _) (cocartesianBaseChangeHomSpanZero l _ _)
    (cocartesianBaseChangeHomSpanOneSection l _ _)
    (isFullyFaithful_of_trivialKanFibration _)
    (cocartesianBaseChangeHomSpanOneSection_projection l _ _)
    (cocartesianBaseChangeSecondTriangleHomFirst l k p q)

end SerrePositivity.InfinityCategories
