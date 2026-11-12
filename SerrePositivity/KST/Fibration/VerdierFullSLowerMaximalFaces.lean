module
public import SerrePositivity.KST.Fibration.VerdierFullSLowerShortFaces

/-!
概要：指定 Verdier 下側二胞体の最大化の短辺を、元の包含・商の全一単体へ戻す。
方針：同じ実三角柱の短辺固定を時刻一で評価し、元の四角形の指定辺を回収する。
規約：二短辺だけを照合する。共有対角と上側二胞体の貼り合わせは別途必要。
使われ方：K-6 c4 の指定下側二胞体を標準合成二胞体へ比較する際の実境界条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 同じ最大化の第一全短辺は、元の下側二胞体の同じ第一辺。 -/
theorem verdierFullSLowerMaximalization_first :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) =
      stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d) := by
  have he : stdSimplex.δ (2 : Fin 3) ≫ SSet.ι₁ =
      SSet.ι₁ ≫ (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) := rfl
  calc
    _ = stdSimplex.δ (2 : Fin 3) ≫ (SSet.ι₁ ≫ (verdierFullSLowerDeformation d).h) :=
      congrArg (stdSimplex.δ (2 : Fin 3) ≫ ·) (verdierFullSLowerDeformation d).h₁.symm
    _ = SSet.ι₁ ≫ ((stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (verdierFullSLowerDeformation d).h) := by rw [← Category.assoc, he, Category.assoc]
    _ = SSet.ι₁ ≫ (fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ stdSimplex.δ (2 : Fin 3) ≫
        SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d)) :=
      congrArg (SSet.ι₁ ≫ ·) (verdierFullSLowerDeformation_first d)
    _ = _ := by rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]

/-- 同じ最大化の第二全短辺は、元の下側二胞体の同じ第二辺。 -/
theorem verdierFullSLowerMaximalization_last :
    stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) =
      stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d) := by
  have he : stdSimplex.δ (0 : Fin 3) ≫ SSet.ι₁ =
      SSet.ι₁ ≫ (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) := rfl
  calc
    _ = stdSimplex.δ (0 : Fin 3) ≫ (SSet.ι₁ ≫ (verdierFullSLowerDeformation d).h) :=
      congrArg (stdSimplex.δ (0 : Fin 3) ≫ ·) (verdierFullSLowerDeformation d).h₁.symm
    _ = SSet.ι₁ ≫ ((stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (verdierFullSLowerDeformation d).h) := by rw [← Category.assoc, he, Category.assoc]
    _ = SSet.ι₁ ≫ (fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ stdSimplex.δ (0 : Fin 3) ≫
        SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d)) :=
      congrArg (SSet.ι₁ ≫ ·) (verdierFullSLowerDeformation_last d)
    _ = _ := by rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]

/-- 同じ最大化の第一辺は、元の指定包含の同じ全 S• Kan 像の全一単体。 -/
theorem verdierFullSLowerMaximalization_inclusion :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0) := by
  rw [verdierFullSLowerMaximalization_first, verdierFullSLowerSimplex_original,
    ← Category.assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge,
    Category.assoc]
  simpa only [Category.assoc] using! congrArg
    (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) d.bottom_edge

/-- 同じ最大化の第二辺は、元の指定商の同じ全 S• Kan 像の全一単体。 -/
theorem verdierFullSLowerMaximalization_projection :
    stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0) := by
  rw [verdierFullSLowerMaximalization_last, verdierFullSLowerSimplex_original,
    ← Category.assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge,
    Category.assoc]
  simpa only [Category.assoc] using! congrArg
    (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) d.right_edge

end SerrePositivity.KST.Fibration
