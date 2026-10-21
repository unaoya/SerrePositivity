module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomSection

/-!
概要：底変換後の分類 Hom を元の底制限の Hom へ運び、同じ元の作用との整合性を示す。
方針：同じ共通 Hom の一射影の切断と零射影を合成し、持ち上げの一意性で四角形を比較する。
規約：比較射の同値性だけでなく、元の全相対 Hom 作用との関手同型を与える。
使われ方：局所の分類 Hom 比較と大域の同じ作用を降下で結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ比較 path を経由して、底変換後の分類 Hom を元の底制限の Hom へ運ぶ。 -/
def cocartesianBaseChangeHomTransport :
    intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) ⟶
      intervalMappingSpace
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram p.val.hom))
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  cocartesianBaseChangeHomSpanOneSection k p q ≫ cocartesianBaseChangeHomSpanZero k p q

/-- 元の同じ比較 path による Hom の輸送は同値。 -/
lemma cocartesianBaseChangeHomTransport_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeHomTransport k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanZero k p q) :=
    cocartesianBaseChangeHomSpanZero_trivialKanFibration k p q
  exact (cocartesianBaseChangeHomSpanOneSection_isQCatEquivalence k p q).comp
    (isQCatEquivalence_of_trivialKanFibration (cocartesianBaseChangeHomSpanZero k p q))

/-- Hom の同じ輸送の四角形は、元の全相対 Hom の作用に関して関手同型で可換。 -/
def cocartesianBaseChangeHomNaturalityIso :
    FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
        cocartesianStraighteningHomInterval
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
            cocartesianBaseChangeHomTransport k p q)
      (cocartesianStraighteningHomInterval p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
          (cocartesianStrictTransportCoherentDiagram p.val.hom)
          (cocartesianStrictTransportCoherentDiagram q.val.hom)) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  let a := (SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
          cocartesianBaseChangeHomSpanOneSection k p q
  let b := cocartesianBaseChangeHomComparison k p q
  have h : a ≫ cocartesianBaseChangeHomSpanOne k p q =
      b ≫ cocartesianBaseChangeHomSpanOne k p q := by
    simp only [a, b, Category.assoc, cocartesianBaseChangeHomSpanOneSection_projection,
      Category.comp_id, cocartesianBaseChangeHomComparison_one]
  let e := (functorIsoOfTrivialKanFibration
    (cocartesianBaseChangeHomSpanOne k p q) a b h).postcomp
      (cocartesianBaseChangeHomSpanZero k p q)
  simpa only [a, b, cocartesianBaseChangeHomTransport, Category.assoc,
    cocartesianBaseChangeHomComparison_zero] using e

end SerrePositivity.InfinityCategories
