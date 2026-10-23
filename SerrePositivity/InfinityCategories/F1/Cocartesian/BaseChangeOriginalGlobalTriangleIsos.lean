module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeOriginalHomTriangleIdentity
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleSecondRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeFirstGlobalNaturalityFactor
public import SerrePositivity.InfinityCategories.F1.FunctorIsoSquareIdentity

/-!
概要：元の全 Hom 上の輸送三角形の四つの指定同型を名前で束ねる。
方針：既存の指定同型に元の同じ比較作用を前合成する。
規約：新しい指定値を選ばない。
使われ方：元の大域三角形の端点を局所自然性と同じ表示へ移す。
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

/-- 元の全 Hom 上の、指定輸送結合同型。 -/
def cocartesianBaseChangeOriginalGlobalCompositionIso :=
  ((cocartesianBaseChangeHomTransport_compositionIso l k p q).precomp
    (cocartesianBaseChangeTriangleHomLong l k p q ≫
      cocartesianBaseChangeHomSpanOne (l ⋙ k) p q)).precomp
        (cocartesianBaseChangeTriangleHomComparison l k p q)

/-- 元の全 Hom 上の、指定直接辺。 -/
def cocartesianBaseChangeOriginalGlobalDirectIso :=
  (cocartesianBaseChangeTransportTriangleDirectIso l k p q).precomp
    (cocartesianBaseChangeTriangleHomComparison l k p q)

/-- 元の全 Hom 上の、同じ制限をした指定第二辺。 -/
def cocartesianBaseChangeOriginalGlobalSecondIso :=
  ((cocartesianBaseChangeTransportTriangleSecondIso l k p q).postcomp
    (cocartesianBaseChangeRestrictedHomTransport l k p q)).precomp
      (cocartesianBaseChangeTriangleHomComparison l k p q)

/-- 元の全 Hom 上の、指定第一辺。 -/
def cocartesianBaseChangeOriginalGlobalFirstIso :=
  (cocartesianBaseChangeTriangleHomFirst_restrictedTransportIso l k p q).precomp
    (cocartesianBaseChangeTriangleHomComparison l k p q)

end SerrePositivity.InfinityCategories
