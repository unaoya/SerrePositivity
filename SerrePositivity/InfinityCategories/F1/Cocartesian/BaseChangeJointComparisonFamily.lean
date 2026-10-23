module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeDiagramComparison
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramArrow
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramRealization

/-!
概要：元の全 fibration の底変換比較を、二点と底全体の Cat∞ 値図式の族へ実現する。
方針：元の全高次 Hom に自然な積上の図式を、同じ core の作用と共同評価で実現する。
規約：底の各対象で構成済みの同じ二つの section 評価を厳密に回収する。
使われ方：同じ分類主写像の底変換との比較を底全体で同時に扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)

/-- 二点と底全体の元の比較を、全 fibration の Cat∞ 値図式の族へ実現する。 -/
def cocartesianBaseChangeJointComparisonFamily :
    CocartesianFibrationInfinity (nerve C) ⟶
      CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 2 × D))) :=
  (cocartesianBaseChangeDiagramComparison k).arrowDiagram.realization

/-- 零側の底の各対象で、元の全 fibration の section 評価を厳密に回収する。 -/
lemma cocartesianBaseChangeJointComparisonFamily_zero (d : D) :
    cocartesianBaseChangeJointComparisonFamily k ≫
      evaluateFunctorAt (ULift.up (nerveVertex ((0 : Fin 2), d))) =
      cocartesianSectionsInfinityEvaluation (Over.mk (nerveMap (Under.forget (k.obj d)))) := by
  rw [cocartesianBaseChangeJointComparisonFamily, QuasicategoryEnrichedDiagram.realization_evaluate]
  rfl

/-- 一側の底の各対象で、元の底変換に続く元の section 評価を厳密に回収する。 -/
lemma cocartesianBaseChangeJointComparisonFamily_one (d : D) :
    cocartesianBaseChangeJointComparisonFamily k ≫
      evaluateFunctorAt (ULift.up (nerveVertex ((1 : Fin 2), d))) =
    cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
      cocartesianSectionsInfinityEvaluation (Over.mk (nerveMap (Under.forget d))) := by
  rw [cocartesianBaseChangeJointComparisonFamily, QuasicategoryEnrichedDiagram.realization_evaluate,
    cocartesianFibrationInfinityBaseChange, cocartesianSectionsInfinityEvaluation,
    ← coherentNerveMap_comp]
  congr 1

end SerrePositivity.InfinityCategories
