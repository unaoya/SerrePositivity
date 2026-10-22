module

public import SerrePositivity.InfinityCategories.F2.Ind.TwistedSourceElementsBaseChange
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensitySourceRestriction
public import SerrePositivity.InfinityCategories.F1.LeftFibrationComparisonBaseChange

/-!
概要：共同 Hom の元の復元射を始点固定に底変換し、同じ密度評価図式へ戻す。
方針：始点固定の全族の厳密な底変換表示と、元の復元射の底変換を続ける。
規約：元の復元射と元の全族を保持する。
使われ方：評価余錐の実際の fiber 写像の弱同値性を検査する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "E" => smallRightUnstraightening F
local notation "p" => smallRightUnstraighteningProjection F
local notation "H" => twistedElementsHomDiagram p
local notation "Dx" => presheafDensityEvaluationDiagram F x

/-- 元の評価図式の unstraightening は、元の共同 Hom の同じ底変換。 -/
def presheafDensityEvaluationUnstraighteningIso : smallLeftUnstraightening Dx ≅
    pullback (smallLeftUnstraighteningProjection H) (presheafDensitySourceInclusion F x) :=
  (smallLeftUnstraighteningMap_isPullback Dx H (presheafDensitySourceInclusion F x)
    (presheafDensitySourceInclusion_source F x)).isoPullback

/-- 元の全復元射を同じ始点固定の全族へ制限した比較。 -/
def presheafDensityEvaluationReconstruction :
    twistedSourceElements p x ⟶ smallLeftUnstraightening Dx :=
  (twistedSourceElementsBaseChangeIso p x).hom ≫
    fiberComparisonBaseChange (twistedElementsProjection p) (smallLeftUnstraighteningProjection H)
      (twistedElementsReconstruction p) (twistedElementsReconstruction_projection p)
      (presheafDensitySourceInclusion F x) ≫ (presheafDensityEvaluationUnstraighteningIso F x).inv

/-- 同じ評価復元射は、元の終点の全空間成分を厳密に保つ。 -/
lemma presheafDensityEvaluationReconstruction_projection :
    presheafDensityEvaluationReconstruction F x ≫ smallLeftUnstraighteningProjection Dx =
      pullback.fst p (twistedArrowSourceProjection x) := by
  rw [presheafDensityEvaluationReconstruction, Category.assoc, Category.assoc,
    show (presheafDensityEvaluationUnstraighteningIso F x).inv ≫
      smallLeftUnstraighteningProjection Dx = _ from
        (smallLeftUnstraighteningMap_isPullback Dx H (presheafDensitySourceInclusion F x)
          (presheafDensitySourceInclusion_source F x)).isoPullback_inv_snd,
    fiberComparisonBaseChange_projection]
  exact twistedSourceElementsBaseChangeIso_snd p x

/-- 同じ評価復元射を全体へ戻すと、元の全復元射の制限そのもの。 -/
lemma presheafDensityEvaluationReconstruction_map :
    presheafDensityEvaluationReconstruction F x ≫
      smallLeftUnstraighteningMap Dx H (presheafDensitySourceInclusion F x)
        (presheafDensitySourceInclusion_source F x) =
      twistedSourceElementsComparison p x ≫ twistedElementsReconstruction p := by
  rw [presheafDensityEvaluationReconstruction, Category.assoc, Category.assoc,
    show (presheafDensityEvaluationUnstraighteningIso F x).inv ≫
      smallLeftUnstraighteningMap Dx H (presheafDensitySourceInclusion F x)
        (presheafDensitySourceInclusion_source F x) = _ from
          (smallLeftUnstraighteningMap_isPullback Dx H (presheafDensitySourceInclusion F x)
            (presheafDensitySourceInclusion_source F x)).isoPullback_inv_fst,
    fiberComparisonBaseChange, pullback.lift_fst, ← Category.assoc]
  exact congrArg (fun f => f ≫ twistedElementsReconstruction p)
    (twistedSourceElementsBaseChangeIso_fst p x)

local instance : Quasicategory E := quasicategory_of_innerFibration p
local instance : Quasicategory (C.op ⊗ E) := quasicategory_of_innerFibration (fst C.op E)
local instance : LeftFibration (twistedElementsProjection p) := by
  rw [← twistedElementsBaseChangeIso_projection p]
  exact ⟨leftFibrations.comp_mem _ _ (leftFibrations.of_isIso (twistedElementsBaseChangeIso p).hom)
    (leftFibrations.pullback_snd _ _
      (show leftFibrations (twistedArrowProjection C) from LeftFibration.mem))⟩

/-- 同じ評価復元射は、任意の Kan 標的への前合成の同値。 -/
lemma presheafDensityEvaluationReconstruction_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (presheafDensityEvaluationReconstruction F x) :=
  (isPrecompositionEquivalence_of_iso (twistedSourceElementsBaseChangeIso p x)).comp
    ((fiberComparisonBaseChange_isPrecompositionEquivalence (twistedElementsProjection p)
      (smallLeftUnstraighteningProjection H) (twistedElementsReconstruction p)
      (twistedElementsReconstruction_projection p)
      (twistedElementsReconstruction_isPrecompositionEquivalence p)
      (presheafDensitySourceInclusion F x)).comp
        (isPrecompositionEquivalence_of_iso (presheafDensityEvaluationUnstraighteningIso F x).symm))

end SerrePositivity.InfinityCategories.F2.Ind
