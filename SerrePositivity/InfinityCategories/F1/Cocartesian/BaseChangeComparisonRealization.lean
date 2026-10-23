module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeComparisonFamily
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryDiagramRealizationEvaluation
public import SerrePositivity.InfinityCategories.F1.Coherent.ResolutionComparisonEdge

/-!
概要：全 fibration の底変換比較を、Cat∞ 値の二点図式の族と実際の比較の辺へ実現する。
方針：同じ図式の族を共同評価で実現し、転置した標準辺の両端を厳密に回収する。
規約：元の section 評価と元の底変換の ∞ 関手を両端に持つ。
使われ方：同じ分類主写像の底変換との coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) (d : D)

/-- 同じ底変換比較の図式の coherent な族を、実際の Cat∞ 値図式の族へ実現する。 -/
def cocartesianBaseChangeComparisonRealization :
    CocartesianFibrationInfinity (nerve C) ⟶ CatInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin 2)))) :=
  cocartesianBaseChangeComparisonFamily k d ≫ quasicategoryDiagramRealization _

/-- 同じ実現の零での評価は、元の全 fibration の section 評価。 -/
lemma cocartesianBaseChangeComparisonRealization_zero :
    cocartesianBaseChangeComparisonRealization k d ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (0 : Fin 2)))) =
      cocartesianSectionsInfinityEvaluation (Over.mk (nerveMap (Under.forget (k.obj d)))) := by
  rw [cocartesianBaseChangeComparisonRealization, Category.assoc,
    quasicategoryDiagramRealization_evaluate]
  exact cocartesianBaseChangeComparisonFamily_zero k d

/-- 同じ実現の一での評価は、元の底変換に続く元の section 評価。 -/
lemma cocartesianBaseChangeComparisonRealization_one :
    cocartesianBaseChangeComparisonRealization k d ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (1 : Fin 2)))) =
    cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
      cocartesianSectionsInfinityEvaluation (Over.mk (nerveMap (Under.forget d))) := by
  rw [cocartesianBaseChangeComparisonRealization, Category.assoc,
    quasicategoryDiagramRealization_evaluate]
  exact cocartesianBaseChangeComparisonFamily_one k d

/-- 元の二つの section 評価の ∞ 関手を両端とする、同じ比較の実際の辺。 -/
def cocartesianBaseChangeComparisonEdge :
    Edge (functorVertex (cocartesianSectionsInfinityEvaluation
      (Over.mk (nerveMap (Under.forget (k.obj d))))))
      (functorVertex (cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
        cocartesianSectionsInfinityEvaluation (Over.mk (nerveMap (Under.forget d))))) :=
  (coherentResolutionComparisonIndexEdge.map
    (transposeFunctorFamily (cocartesianBaseChangeComparisonRealization k d))).ofEq
    (by rw [transposeFunctorFamily_vertex, cocartesianBaseChangeComparisonRealization_zero])
    (by rw [transposeFunctorFamily_vertex, cocartesianBaseChangeComparisonRealization_one])

end SerrePositivity.InfinityCategories
