module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSimplicialHomComparison

/-!
概要：元の比較 path の底制限後の Hom span と、元の分類図式の同じ底制限への評価。
方針：元の二つの端点をそのまま同じ底で制限する。
規約：元の二つの分類図式全体と全高次の Hom を保持する。
使われ方：元の既存の Hom 輸送の制限に関する自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {D C : Type u} [Category.{u} D] [Category.{u} C]
  {A : SSet.{u + 1}} (a : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve D)) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ制限した比較 Hom の零評価は、元の分類図式を同じ二つの底の射で制限した Hom。 -/
def cocartesianBaseChangeSimplicialHomSpanZero :
    cocartesianBaseChangeSimplicialHomComparisonSpace a k p q ⟶ intervalMappingSpace
      (functorVertex (a ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex (a ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  intervalHomPathEndpoint (cocartesianBaseChangeSimplicialHomPath a k) 0
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeSimplicialHomPath_zero_vertex a k p)
    (cocartesianBaseChangeSimplicialHomPath_zero_vertex a k q)

/-- 同じ制限した比較 Hom の一評価は、元の底変換対象の分類図式を同じ底で制限した Hom。 -/
def cocartesianBaseChangeSimplicialHomSpanOne :
    cocartesianBaseChangeSimplicialHomComparisonSpace a k p q ⟶ intervalMappingSpace
      (functorVertex (a ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex (a ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) :=
  intervalHomPathEndpoint (cocartesianBaseChangeSimplicialHomPath a k) 1
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeSimplicialHomPath_one_vertex a k p)
    (cocartesianBaseChangeSimplicialHomPath_one_vertex a k q)

/-- 同じ制限した比較 Hom の零射影は全境界を持ち上げる。 -/
lemma cocartesianBaseChangeSimplicialHomSpanZero_trivialKanFibration :
    TrivialKanFibration (cocartesianBaseChangeSimplicialHomSpanZero a k p q) :=
  intervalHomPathEndpoint_trivialKanFibration _ _ _ _ _ _

/-- 同じ制限した比較 Hom の一射影は全境界を持ち上げる。 -/
lemma cocartesianBaseChangeSimplicialHomSpanOne_trivialKanFibration :
    TrivialKanFibration (cocartesianBaseChangeSimplicialHomSpanOne a k p q) :=
  intervalHomPathEndpoint_trivialKanFibration _ _ _ _ _ _

end SerrePositivity.InfinityCategories
