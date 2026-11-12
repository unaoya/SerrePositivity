module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningSectionsIso
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.CommonWeightedHomAction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorExponentialEvaluation
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorPostUncurry
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RelativeConstFiberEvaluation

/-!
概要：元の小さい切断と大きい切断の比較を、元の全空間の評価で計算する。
方針：相対関手の宇宙移送、底上の同型、切断表示の三つの評価式を合成する。
規約：元の縮小同型を保持する。別の切断比較には置き換えない。
使われ方：実際の形状制限との厳密な自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 元の大小の切断比較は、全評価を元の全空間の縮小同型で結ぶ。 -/
lemma smallUnstraighteningSectionsIso_evaluation {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj B ◁ (smallUnstraighteningSectionsIso F).hom) ≫
      simplicialSectionsEvaluation (leftUnstraighteningProjection F) =
    (uliftTensorIso B (simplicialSections (smallLeftUnstraighteningProjection F))).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (simplicialSectionsEvaluation (smallLeftUnstraighteningProjection F)) ≫
      (smallLeftUnstraighteningIso F).hom := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let p := smallLeftUnstraighteningProjection F
  let q := U.map (simplicialSectionsRelativeIso p).hom ≫
    (uliftRelativeFunctorIso p (𝟙 B)).hom ≫
      eqToHom (congrArg (relativeFunctorSpace (U.map p)) (U.map_id B))
  change (U.obj B ◁ ((q ≫ (relativeFunctorOverIso
    (Iso.refl (Over.mk (𝟙 (U.obj B)))) (smallLeftUnstraighteningOverIso F)).hom) ≫
      (simplicialSectionsRelativeIso (leftUnstraighteningProjection F)).inv)) ≫ _ = _
  erw [simplicialSectionsRelativeIso_inv_evaluation, relativeFunctorOverIso_hom]
  simp only [Iso.refl_inv, relativeFunctorOverPre_id, Category.id_comp]
  erw [relativeFunctorPost_uncurry]
  dsimp only [q]
  rw [← Category.assoc]
  erw [relativeFunctorUncurry_transport (U.map p) (U.map_id B)]
  rw [uliftRelativeFunctorMap_uncurry]
  simp only [Category.assoc]
  change (uliftTensorIso B (simplicialSections p)).inv ≫
    U.map (relativeFunctorUncurry (simplicialSectionsRelativeIso p).hom) ≫ _ = _
  have hp : relativeFunctorUncurry (simplicialSectionsRelativeIso p).hom =
      simplicialSectionsEvaluation p := relativeFunctorUncurry_curry _
        (by simp only [Category.comp_id, simplicialSectionsEvaluation_projection])
  rw [hp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
