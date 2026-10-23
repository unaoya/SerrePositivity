module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityHomComparison
public import SerrePositivity.InfinityCategories.F1.IntervalHomPathSpan

/-!
概要：元の結合比較 Hom の両評価は、二回と直接の底変換対象の分類 Hom を結ぶ。
方針：同じ path の両端評価を元の分類図式の頂点へ正規化する。
規約：元の二回・直接の底変換対象そのもの。
使われ方：元の結合比較辺による Hom 輸送。
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

/-- 同じ結合比較 Hom の零評価は、元の二回の底変換対象の分類 Hom への射影。 -/
def cocartesianBaseChangeAssociativityHomSpanZero :
    cocartesianBaseChangeAssociativityHomComparisonSpace l k p q ⟶ intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)).val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)).val.hom)) :=
  intervalHomPathEndpoint (cocartesianBaseChangeAssociativityHomPath l k) 0
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeAssociativityHomPath_zero_vertex l k p)
    (cocartesianBaseChangeAssociativityHomPath_zero_vertex l k q)

/-- 同じ結合比較 Hom の一評価は、元の直接の底変換対象の分類 Hom への射影。 -/
def cocartesianBaseChangeAssociativityHomSpanOne :
    cocartesianBaseChangeAssociativityHomComparisonSpace l k p q ⟶ intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p).val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q).val.hom)) :=
  intervalHomPathEndpoint (cocartesianBaseChangeAssociativityHomPath l k) 1
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeAssociativityHomPath_one_vertex l k p)
    (cocartesianBaseChangeAssociativityHomPath_one_vertex l k q)

/-- 同じ結合比較 Hom の零射影は全境界を持ち上げる。 -/
lemma cocartesianBaseChangeAssociativityHomSpanZero_trivialKanFibration :
    TrivialKanFibration (cocartesianBaseChangeAssociativityHomSpanZero l k p q) :=
  intervalHomPathEndpoint_trivialKanFibration _ _ _ _ _ _

/-- 同じ結合比較 Hom の一射影は全境界を持ち上げる。 -/
lemma cocartesianBaseChangeAssociativityHomSpanOne_trivialKanFibration :
    TrivialKanFibration (cocartesianBaseChangeAssociativityHomSpanOne l k p q) :=
  intervalHomPathEndpoint_trivialKanFibration _ _ _ _ _ _

end SerrePositivity.InfinityCategories
