module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomNaturalityLift
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransport

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

/-- 同じ持ち上げの零射影は、元の底変換 Hom 作用に続く指定 Hom 輸送。 -/
lemma cocartesianBaseChangeHomNaturalityLift_zero_transport :
    cocartesianBaseChangeHomNaturalityLift k p q ≫ cocartesianBaseChangeHomSpanZero k p q =
    (SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
        cocartesianStraighteningHomInterval
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
            cocartesianBaseChangeHomTransport k p q := by
  simp only [cocartesianBaseChangeHomNaturalityLift, cocartesianBaseChangeHomTransport,
    Category.assoc]

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
  exact F2.functorIsoOfEq ((cocartesianBaseChangeHomNaturalityLiftIso k p q).postcomp
    (cocartesianBaseChangeHomSpanZero k p q))
    (cocartesianBaseChangeHomNaturalityLift_zero_transport k p q)
    (cocartesianBaseChangeHomComparison_zero k p q)

end SerrePositivity.InfinityCategories
