module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondHomPath
public import SerrePositivity.InfinityCategories.F1.IntervalHomPathSpan

/-!
概要：元の比較三角形の第二面の同じ Hom span。
方針：元の第二面の path を両端で評価し、元の分類図式へ正規化する。
規約：元の全対象・全高次の第二面そのもの。
使われ方：二段の元の Hom 輸送を、元の比較三角形の第二面へ降ろす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の二つの fibration での同じ第二面の全 Hom。 -/
def cocartesianBaseChangeSecondHomComparisonSpace : SSet.{u + 1} :=
  intervalMappingSpace
    ((cocartesianBaseChangeSecondHomPath l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeSecondHomPath l k).app _ (coherentNerveVertex q))

/-- 元の同じ第二面の Hom は Kan 複体。 -/
instance cocartesianBaseChangeSecondHomComparisonSpace_kanComplex :
    KanComplex (cocartesianBaseChangeSecondHomComparisonSpace l k p q) := by
  change KanComplex (intervalMappingSpace
    ((cocartesianBaseChangeSecondHomPath l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeSecondHomPath l k).app _ (coherentNerveVertex q)))
  infer_instance

/-- 元の同じ第二面の零射影は、底変換対象の分類図式の底制限の Hom へ評価する。 -/
def cocartesianBaseChangeSecondHomSpanZero :
    cocartesianBaseChangeSecondHomComparisonSpace l k p q ⟶ intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) :=
  intervalHomPathEndpoint (cocartesianBaseChangeSecondHomPath l k) 0
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeSecondHomPath_zero_vertex l k p)
    (cocartesianBaseChangeSecondHomPath_zero_vertex l k q)

/-- 元の同じ第二面の一射影は、直接の底変換対象の分類 Hom へ評価する。 -/
def cocartesianBaseChangeSecondHomSpanOne :
    cocartesianBaseChangeSecondHomComparisonSpace l k p q ⟶ intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p).val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q).val.hom)) :=
  intervalHomPathEndpoint (cocartesianBaseChangeSecondHomPath l k) 1
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeSecondHomPath_one_vertex l k p)
    (cocartesianBaseChangeSecondHomPath_one_vertex l k q)

/-- 元の第二面の零射影は全境界を持ち上げる。 -/
lemma cocartesianBaseChangeSecondHomSpanZero_trivialKanFibration :
    TrivialKanFibration (cocartesianBaseChangeSecondHomSpanZero l k p q) :=
  intervalHomPathEndpoint_trivialKanFibration _ _ _ _ _ _

/-- 元の第二面の一射影は全境界を持ち上げる。 -/
lemma cocartesianBaseChangeSecondHomSpanOne_trivialKanFibration :
    TrivialKanFibration (cocartesianBaseChangeSecondHomSpanOne l k p q) :=
  intervalHomPathEndpoint_trivialKanFibration _ _ _ _ _ _

end SerrePositivity.InfinityCategories
