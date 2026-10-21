module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleHomMiddle
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityHomTransport
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomTransport

/-!
概要：同じ分解三角形の共通 Hom 上で、既存の二回目の輸送と元の結合比較の輸送を合成する。
方針：元の中間 Hom の厳密な一致と、指定された元の切断の比較を使う。
規約：既存の cocartesianBaseChangeHomTransport を選び直さない。
使われ方：元の第二面の輸送を実際の二段の Hom 輸送へ接続する。
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

/-- 同じ共通 Hom から、元の直接の底変換対象の分類 Hom への射影は同値。 -/
lemma cocartesianBaseChangeSecondTriangleHomSecond_one_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeSecondTriangleHomSecond l k p q ≫
      cocartesianBaseChangeAssociativityHomSpanOne l k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeAssociativityHomSpanOne l k p q) :=
    cocartesianBaseChangeAssociativityHomSpanOne_trivialKanFibration l k p q
  exact (cocartesianBaseChangeSecondTriangleHomSecond_isQCatEquivalence l k p q).comp
    (isQCatEquivalence_of_trivialKanFibration _)

/-- 同じ共通 Hom 上で、元の結合比較辺の輸送は同じ両端評価を結ぶ。 -/
def cocartesianBaseChangeSecondTriangleHomAssociativityTransportIso :
    FunctorIso
      ((cocartesianBaseChangeSecondTriangleHomSecond l k p q ≫
        cocartesianBaseChangeAssociativityHomSpanOne l k p q) ≫
          cocartesianBaseChangeAssociativityHomTransport l k p q)
      (cocartesianBaseChangeSecondTriangleHomSecond l k p q ≫
        cocartesianBaseChangeAssociativityHomSpanZero l k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeAssociativityHomSpanOne l k p q) :=
    cocartesianBaseChangeAssociativityHomSpanOne_trivialKanFibration l k p q
  exact homSpanSectionTransportFactorIso
    (cocartesianBaseChangeAssociativityHomSpanOne l k p q)
    (cocartesianBaseChangeAssociativityHomSpanZero l k p q)
    (cocartesianBaseChangeAssociativityHomSpanOneSection l k p q)
    (isFullyFaithful_of_trivialKanFibration _)
    (cocartesianBaseChangeAssociativityHomSpanOneSection_projection l k p q)
    (cocartesianBaseChangeSecondTriangleHomSecond l k p q)

/-- 同じ共通 Hom 上で、元の結合比較と既存の二回目の Hom 輸送の合成は元の両評価を結ぶ。 -/
def cocartesianBaseChangeSecondTriangleHomCompositeTransportIso :
    FunctorIso
      ((cocartesianBaseChangeSecondTriangleHomSecond l k p q ≫
        cocartesianBaseChangeAssociativityHomSpanOne l k p q) ≫
        (cocartesianBaseChangeAssociativityHomTransport l k p q ≫
          cocartesianBaseChangeHomTransport l
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))
      (cocartesianBaseChangeSecondTriangleHomFirst l k p q ≫
        cocartesianBaseChangeHomSpanZero l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) := by
  have e := cocartesianBaseChangeSecondTriangleHomAssociativityTransportIso l k p q
  rw [← cocartesianBaseChangeSecondTriangleHom_middle l k p q] at e
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne l
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration l _ _
  have e' := homSpanSectionTransportFactorIso
    (cocartesianBaseChangeHomSpanOne l _ _) (cocartesianBaseChangeHomSpanZero l _ _)
    (cocartesianBaseChangeHomSpanOneSection l _ _)
    (isFullyFaithful_of_trivialKanFibration _)
    (cocartesianBaseChangeHomSpanOneSection_projection l _ _)
    (cocartesianBaseChangeSecondTriangleHomFirst l k p q)
  simpa only [Category.assoc] using
    e.postcomp (cocartesianBaseChangeHomTransport l _ _) ≪≫ e'

end SerrePositivity.InfinityCategories
