module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientEvaluationReconstruction
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeRestriction

/-!
概要：元の全復元射を、指定 native 評価図式そのものを底として係数・始点へ制限する。
方針：同じ始点固定族の引き戻しと、同じ共同復元の底変換を使う。
規約：元の native 評価図式を保つ。使われ方：実際の評価余錐の相対像を同じ族へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C) (i : I) (x : C _⦋0⦌)
local notation "ρ" => weightedDensityProjection F
local notation "H" => twistedElementsHomDiagram ρ
local notation "D" => weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "g" => weightedCoefficientEvaluationBase F i x

/-- 元の native 評価図式を、元の全復元射の同じ係数・始点への底変換で復元する。 -/
def weightedCoefficientNativeReconstruction : twistedSourceElements (F.obj i).val.hom x ⟶
    smallLeftUnstraightening D :=
  (weightedCoefficientSourceIntoTotal_isPullback F i x).isoPullback.hom ≫
    fiberComparisonBaseChange (twistedElementsProjection ρ) (smallLeftUnstraighteningProjection H)
      (twistedElementsReconstruction ρ) (twistedElementsReconstruction_projection ρ) g ≫
        (smallLeftUnstraighteningMap_isPullback D H g
          (weightedCoefficientNativeEvaluationBase_source κ F i x)).isoPullback.inv

/-- 同じ native 評価の復元は、元の係数全空間成分を厳密に保つ。 -/
lemma weightedCoefficientNativeReconstruction_projection :
    weightedCoefficientNativeReconstruction κ F i x ≫ smallLeftUnstraighteningProjection D =
      pullback.fst (F.obj i).val.hom (twistedArrowSourceProjection x) := by
  rw [weightedCoefficientNativeReconstruction, Category.assoc, Category.assoc,
    (smallLeftUnstraighteningMap_isPullback D H g
      (weightedCoefficientNativeEvaluationBase_source κ F i x)).isoPullback_inv_snd,
    fiberComparisonBaseChange_projection]
  exact (weightedCoefficientSourceIntoTotal_isPullback F i x).isoPullback_hom_snd

/-- 元の共同全空間へ戻すと、元の全復元射の同じ係数・始点制限そのもの。 -/
lemma weightedCoefficientNativeReconstruction_map :
    weightedCoefficientNativeReconstruction κ F i x ≫ smallLeftUnstraighteningMap D H g
      (weightedCoefficientNativeEvaluationBase_source κ F i x) =
      weightedCoefficientSourceIntoTotal F i x ≫ twistedElementsReconstruction ρ := by
  rw [weightedCoefficientNativeReconstruction, Category.assoc, Category.assoc,
    (smallLeftUnstraighteningMap_isPullback D H g
      (weightedCoefficientNativeEvaluationBase_source κ F i x)).isoPullback_inv_fst,
    fiberComparisonBaseChange, pullback.lift_fst, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ twistedElementsReconstruction ρ)
    (weightedCoefficientSourceIntoTotal_isPullback F i x).isoPullback_hom_fst

/-- 元の native 評価図式への同じ復元射自身は、追加仮定なしに前合成同値。 -/
lemma weightedCoefficientNativeReconstruction_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (weightedCoefficientNativeReconstruction κ F i x) := by
  letI := weightedCoefficientEvaluationWeighted_quasicategory F
  letI := weightedCoefficientEvaluationJointBase_quasicategory F
  letI := weightedCoefficientTwistedProjection_leftFibration F
  exact (isPrecompositionEquivalence_of_iso
    (weightedCoefficientSourceIntoTotal_isPullback F i x).isoPullback).comp
      ((fiberComparisonBaseChange_isPrecompositionEquivalence (twistedElementsProjection ρ)
        (smallLeftUnstraighteningProjection H) (twistedElementsReconstruction ρ)
        (twistedElementsReconstruction_projection ρ)
        (twistedElementsReconstruction_isPrecompositionEquivalence ρ) g).comp
          (isPrecompositionEquivalence_of_iso (smallLeftUnstraighteningMap_isPullback D H g
            (weightedCoefficientNativeEvaluationBase_source κ F i x)).isoPullback.symm))

end SerrePositivity.InfinityCategories.F2.Ind
