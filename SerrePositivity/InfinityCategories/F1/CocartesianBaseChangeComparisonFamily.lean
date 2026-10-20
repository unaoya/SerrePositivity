module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeEnrichedComparison
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedComparisonArrow

/-!
概要：底変換比較の二点図式を、全 fibration の coherent な族へ束ねる。
方針：元の豊穣比較の全 Hom の作用に core と coherent nerve を適用する。
規約：零と一の評価は元の section 評価と元の底変換後の評価を厳密に回収する。
使われ方：分類主写像の底変換との比較を、全 fibration で同時に実現する入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) (d : D)

/-- 元の全 Hom の core に作用する、底変換比較の二点図式への豊穣関手。 -/
def cocartesianBaseChangeComparisonCoreEnriched :
    EnrichedFunctor SSet.{u} (CocartesianFibrationCategory (nerve C))
      (QuasicategoryDiagramCategory (ULift.{u} (Fin 2))) :=
  quasicategoryCoreEnrichedFunctor
    (quasicategoryEnrichedComparisonArrowEnriched (cocartesianBaseChangeEnrichedComparison k d))

/-- 同じ底変換比較の全対象・全高次からなる coherent な二点図式の族。 -/
def cocartesianBaseChangeComparisonFamily :
    CocartesianFibrationInfinity (nerve C) ⟶
      SimplicialNerve (QuasicategoryDiagramCategory (ULift.{u} (Fin 2))) :=
  coherentNerveMap (cocartesianBaseChangeComparisonCoreEnriched k d)

/-- 同じ比較の族の零での評価は、元の全 fibration の元の section 評価。 -/
lemma cocartesianBaseChangeComparisonFamily_zero :
    cocartesianBaseChangeComparisonFamily k d ≫
      coherentNerveMap (quasicategoryDiagramCoreEvaluationEnriched (ULift.up (0 : Fin 2))) =
      cocartesianSectionsInfinityEvaluation (Over.mk (nerveMap (Under.forget (k.obj d)))) := by
  rw [cocartesianBaseChangeComparisonFamily, cocartesianSectionsInfinityEvaluation,
    ← coherentNerveMap_comp]
  congr 1

/-- 同じ比較の族の一での評価は、元の底変換の ∞ 関手に続く元の section 評価。 -/
lemma cocartesianBaseChangeComparisonFamily_one :
    cocartesianBaseChangeComparisonFamily k d ≫
      coherentNerveMap (quasicategoryDiagramCoreEvaluationEnriched (ULift.up (1 : Fin 2))) =
    cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
      cocartesianSectionsInfinityEvaluation (Over.mk (nerveMap (Under.forget d))) := by
  rw [cocartesianBaseChangeComparisonFamily, cocartesianFibrationInfinityBaseChange,
    cocartesianSectionsInfinityEvaluation, ← coherentNerveMap_comp, ← coherentNerveMap_comp]
  congr 1

end SerrePositivity.InfinityCategories
