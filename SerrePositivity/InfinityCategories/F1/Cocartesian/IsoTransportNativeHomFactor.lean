module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportNativeHomOne
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityHomTransport

/-!
概要：全局所の結合 Hom 比較に使う同じ span の指定因子比較を明示する。
方針：元の一射影の指定切断と同じ比較作用を用いる。
規約：既存の結合輸送の指定同型を選び直さない。
使われ方：元の大域作用上の第二面の結合因子を照合する。
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

/-- 元の結合比較 span の一射影は充満忠実。 -/
lemma cocartesianBaseChangeAssociativityHomSpanOne_isFullyFaithful :
    IsFullyFaithful (cocartesianBaseChangeAssociativityHomSpanOne l k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeAssociativityHomSpanOne l k p q) :=
    cocartesianBaseChangeAssociativityHomSpanOne_trivialKanFibration l k p q
  exact isFullyFaithful_of_trivialKanFibration _

/-- 全局所 Hom の同じ結合比較に対する、既存の指定切断の因子比較。 -/
def cocartesianIsoTransportNativeHomFactorIso :
    FunctorIso
      ((cocartesianIsoTransportNativeHomComparison l k p q ≫
        cocartesianBaseChangeAssociativityHomSpanOne l k p q) ≫
          cocartesianBaseChangeAssociativityHomTransport l k p q)
      (cocartesianIsoTransportNativeHomComparison l k p q ≫
        cocartesianBaseChangeAssociativityHomSpanZero l k p q) :=
  homSpanSectionTransportFactorIso
    (cocartesianBaseChangeAssociativityHomSpanOne l k p q)
    (cocartesianBaseChangeAssociativityHomSpanZero l k p q)
    (cocartesianBaseChangeAssociativityHomSpanOneSection l k p q)
    (cocartesianBaseChangeAssociativityHomSpanOne_isFullyFaithful l k p q)
    (cocartesianBaseChangeAssociativityHomSpanOneSection_projection l k p q)
    (cocartesianIsoTransportNativeHomComparison l k p q)

end SerrePositivity.InfinityCategories
