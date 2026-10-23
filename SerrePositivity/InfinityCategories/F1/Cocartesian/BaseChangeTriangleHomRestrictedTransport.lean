module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomFirst
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictedHomTransport
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomSpanSectionTransport

/-!
概要：元の比較三角形の Hom 上で、最初の面の同じ制限した Hom 輸送を回収する。
方針：元の最初の面への射影と、同じ制限した比較 span の指定切断を使う。
規約：元の比較 path の底制限を保持する。
使われ方：元の直接の Hom 輸送を含む三角形則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の同じ三角形の Hom 上で、最初の面の輸送は元の同じ二評価を結ぶ。 -/
def cocartesianBaseChangeTriangleHomFirst_restrictedTransportIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      ((cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanOne l k p q) ≫
          cocartesianBaseChangeRestrictedHomTransport l k p q)
      (cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanZero l k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeRestrictedHomSpanOne l k p q) :=
    cocartesianBaseChangeRestrictedHomSpanOne_trivialKanFibration l k p q
  exact homSpanSectionTransportFactorIso
    (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q)
    (isFullyFaithful_of_trivialKanFibration _)
    (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q)
    (cocartesianBaseChangeTriangleHomFirst l k p q)

end SerrePositivity.InfinityCategories
