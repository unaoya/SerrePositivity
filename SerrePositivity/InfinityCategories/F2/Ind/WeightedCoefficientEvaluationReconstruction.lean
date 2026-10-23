module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientSourcePullback
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationComparisonBaseChange

/-!
概要：元の全 twisted-arrow 復元射を係数・始点へ底変換し、同じ評価図式を復元する。
方針：同じ始点固定族の引き戻し表示と、元の共同復元射の底変換を合成する。
規約：元の復元射と同じ族を保持。使われ方：実際の評価余錐の fiber 写像との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I) (x : C _⦋0⦌)
local notation "ρ" => weightedDensityProjection F
local notation "H" => twistedElementsHomDiagram ρ
local notation "D" => weightedCoefficientEvaluationDiagram F i x
local notation "g" => weightedCoefficientEvaluationBase F i x

/-- 同じ全復元射から、元の係数の始点固定族上で得る同じ評価図式への復元。 -/
def weightedCoefficientEvaluationReconstruction : twistedSourceElements (F.obj i).val.hom x ⟶
    smallLeftUnstraightening D :=
  (weightedCoefficientSourceIntoTotal_isPullback F i x).isoPullback.hom ≫
    fiberComparisonBaseChange (twistedElementsProjection ρ) (smallLeftUnstraighteningProjection H)
      (twistedElementsReconstruction ρ) (twistedElementsReconstruction_projection ρ) g ≫
        (smallLeftUnstraighteningMap_isPullback D H g
          (weightedCoefficientEvaluationBase_source F i x)).isoPullback.inv

/-- 同じ復元は、元の係数の全空間成分を厳密に保つ。 -/
lemma weightedCoefficientEvaluationReconstruction_projection :
    weightedCoefficientEvaluationReconstruction F i x ≫ smallLeftUnstraighteningProjection D =
      pullback.fst (F.obj i).val.hom (twistedArrowSourceProjection x) := by
  rw [weightedCoefficientEvaluationReconstruction, Category.assoc, Category.assoc,
    (smallLeftUnstraighteningMap_isPullback D H g
      (weightedCoefficientEvaluationBase_source F i x)).isoPullback_inv_snd,
    fiberComparisonBaseChange_projection]
  exact (weightedCoefficientSourceIntoTotal_isPullback F i x).isoPullback_hom_snd

/-- 元の全空間へ戻すと、元の全復元射の同じ係数・始点での制限そのもの。 -/
lemma weightedCoefficientEvaluationReconstruction_map :
    weightedCoefficientEvaluationReconstruction F i x ≫ smallLeftUnstraighteningMap D H g
      (weightedCoefficientEvaluationBase_source F i x) =
      weightedCoefficientSourceIntoTotal F i x ≫ twistedElementsReconstruction ρ := by
  rw [weightedCoefficientEvaluationReconstruction, Category.assoc, Category.assoc,
    (smallLeftUnstraighteningMap_isPullback D H g
      (weightedCoefficientEvaluationBase_source F i x)).isoPullback_inv_fst,
    fiberComparisonBaseChange, pullback.lift_fst, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ twistedElementsReconstruction ρ)
    (weightedCoefficientSourceIntoTotal_isPullback F i x).isoPullback_hom_fst

local instance weightedCoefficientEvaluationWeighted_quasicategory :
    Quasicategory (weightedNerve (rightFibrationTotalDiagram F)) := by
  have (j : I) : Quasicategory ((rightFibrationTotalDiagram F).obj j) :=
    quasicategory_of_innerFibration (F.obj j).val.hom
  infer_instance

local instance weightedCoefficientEvaluationJointBase_quasicategory :
    Quasicategory (C.op ⊗ weightedNerve (rightFibrationTotalDiagram F)) :=
  quasicategory_of_innerFibration (fst C.op (weightedNerve (rightFibrationTotalDiagram F)))

local instance weightedCoefficientTwistedProjection_leftFibration :
    LeftFibration (twistedElementsProjection ρ) := by
  rw [← twistedElementsBaseChangeIso_projection ρ]
  exact ⟨leftFibrations.comp_mem _ _
    (leftFibrations.of_isIso (twistedElementsBaseChangeIso ρ).hom)
    (leftFibrations.pullback_snd _ _
      (show leftFibrations (twistedArrowProjection C) from LeftFibration.mem))⟩

/-- 同じ評価復元射自身は、追加の同値性仮定なしに前合成同値。 -/
lemma weightedCoefficientEvaluationReconstruction_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (weightedCoefficientEvaluationReconstruction F i x) :=
  (isPrecompositionEquivalence_of_iso
    (weightedCoefficientSourceIntoTotal_isPullback F i x).isoPullback).comp
      ((fiberComparisonBaseChange_isPrecompositionEquivalence (twistedElementsProjection ρ)
        (smallLeftUnstraighteningProjection H) (twistedElementsReconstruction ρ)
        (twistedElementsReconstruction_projection ρ)
        (twistedElementsReconstruction_isPrecompositionEquivalence ρ) g).comp
          (isPrecompositionEquivalence_of_iso (smallLeftUnstraighteningMap_isPullback D H g
            (weightedCoefficientEvaluationBase_source F i x)).isoPullback.symm))

end SerrePositivity.InfinityCategories.F2.Ind
