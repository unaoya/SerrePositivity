module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomTransport
public import SerrePositivity.InfinityCategories.F1.HomSpanSectionTransport

/-!
概要：同じ元の比較三角形の共通 Hom は、既存の直接の Hom 輸送と整合する。
方針：既存の一射影の元の切断を保持して、同じ長辺へ射影する。
規約：構成済みの cocartesianBaseChangeHomTransport を選び直さない。
使われ方：元の底変換 Hom 輸送の三角形則の長辺。
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

/-- 同じ三角形の長辺を既存の直接の終点 Hom で評価する射影は同値。 -/
lemma cocartesianBaseChangeTriangleHomLong_one_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeTriangleHomLong l k p q ≫
      cocartesianBaseChangeHomSpanOne (l ⋙ k) p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne (l ⋙ k) p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration (l ⋙ k) p q
  exact (cocartesianBaseChangeTriangleHomLong_isQCatEquivalence l k p q).comp
    (isQCatEquivalence_of_trivialKanFibration _)

/-- 元の同じ三角形の Hom 上で、既存の直接の切断による Hom 輸送は元の両評価を結ぶ。 -/
def cocartesianBaseChangeTriangleHomLong_transportIso :
    FunctorIso
      ((cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q) ≫
          cocartesianBaseChangeHomTransport (l ⋙ k) p q)
      (cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanZero (l ⋙ k) p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne (l ⋙ k) p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration (l ⋙ k) p q
  exact homSpanSectionTransportFactorIso
    (cocartesianBaseChangeHomSpanOne (l ⋙ k) p q)
    (cocartesianBaseChangeHomSpanZero (l ⋙ k) p q)
    (cocartesianBaseChangeHomSpanOneSection (l ⋙ k) p q)
    (isFullyFaithful_of_trivialKanFibration _)
    (cocartesianBaseChangeHomSpanOneSection_projection (l ⋙ k) p q)
    (cocartesianBaseChangeTriangleHomLong l k p q)

end SerrePositivity.InfinityCategories
