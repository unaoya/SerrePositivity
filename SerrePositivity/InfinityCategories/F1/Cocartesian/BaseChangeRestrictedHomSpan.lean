module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictedHomComparison

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

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ制限した比較 Hom の零評価は、元の分類図式を同じ二つの底の射で制限した Hom。 -/
def cocartesianBaseChangeRestrictedHomSpanZero :
    cocartesianBaseChangeRestrictedHomComparisonSpace l k p q ⟶ intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  intervalHomPathEndpoint (cocartesianBaseChangeRestrictedHomPath l k) 0
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeRestrictedHomPath_zero_vertex l k p)
    (cocartesianBaseChangeRestrictedHomPath_zero_vertex l k q)

/-- 同じ制限した比較 Hom の一評価は、元の底変換対象の分類図式を同じ底で制限した Hom。 -/
def cocartesianBaseChangeRestrictedHomSpanOne :
    cocartesianBaseChangeRestrictedHomComparisonSpace l k p q ⟶ intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) :=
  intervalHomPathEndpoint (cocartesianBaseChangeRestrictedHomPath l k) 1
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeRestrictedHomPath_one_vertex l k p)
    (cocartesianBaseChangeRestrictedHomPath_one_vertex l k q)

/-- 同じ制限した比較 Hom の零射影は全境界を持ち上げる。 -/
lemma cocartesianBaseChangeRestrictedHomSpanZero_trivialKanFibration :
    TrivialKanFibration (cocartesianBaseChangeRestrictedHomSpanZero l k p q) :=
  intervalHomPathEndpoint_trivialKanFibration _ _ _ _ _ _

/-- 同じ制限した比較 Hom の一射影は全境界を持ち上げる。 -/
lemma cocartesianBaseChangeRestrictedHomSpanOne_trivialKanFibration :
    TrivialKanFibration (cocartesianBaseChangeRestrictedHomSpanOne l k p q) :=
  intervalHomPathEndpoint_trivialKanFibration _ _ _ _ _ _

end SerrePositivity.InfinityCategories
