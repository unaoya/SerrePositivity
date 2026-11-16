module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceParameters
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOppositeInverseNaturality
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso

/-!
概要：元の全source-frame augmentationの同じ逆を、元の全実射の始域へ引き戻す。
方針：同じ反対添字とnerve反転の自然性で元の全augmentationを前合成する。
規約：対象ごとに逆を選ばず、同じ全augmentationの一つのFunctorIsoを使う。
使われ方：元の全pairingの始域から元の試験対象への正規化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
variable (A : Type u) [CommRing A]
local instance jointSourceAugComparisonModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointSourceAugComparisonFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の全実射の始域のnativeな反変の全図式。 -/
def strictBETotJointSourceNativeDomain :
    nerve (StrictBETotJointSourceElements A) ⟶ (CAlg_R A).op :=
  nerveMap (FrameHom.liftedSourceFrameArrowDomain (strictBETotJointSourceFrame A)
    (rightFrameReplacement (rightFrameFamily A))) ≫
      (nerveOppositeIso (C := AsSmall.{u+1} (operad A).Algebra)).inv ≫
        SSet.opFunctor.map (strictBETotModelSource A)

/-- 同じ全実射の元の試験対象のnativeな反変の全図式。 -/
def strictBETotJointSourceOriginalNativeDomain :
    nerve (StrictBETotJointSourceElements A) ⟶ (CAlg_R A).op :=
  nerveMap (strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomSourceIndex A) ≫
    (nerveOppositeIso (C := AsSmall.{u+1} (operad A).Algebra)).inv ≫
      SSet.opFunctor.map (strictBETotModelSource A)

/-- 元の全augmentationへの同じ反対添字の全nerve入力。 -/
def strictBETotJointSourceAugmentationInput :
    nerve (StrictBETotJointSourceElements A) ⟶ (nerve (strictBETotJointSourceFrameIndex A)).op :=
  nerveMap (strictBETotJointSourceParameterIndex A) ≫
    (nerveOppositeIso (C := strictBETotJointSourceFrameIndex A)).inv

/-- 同じ元の全augmentationの評価端は、元の実射の始域へ戻る。 -/
theorem strictBETotJointSourceAugmentationInput_evaluation :
    strictBETotJointSourceAugmentationInput A ≫
      SSet.opFunctor.map (nerveMap (strictBETotJointSourceFrameEvaluation A) ≫
        strictBETotModelSource A) = strictBETotJointSourceNativeDomain A := by
  rw [SSet.opFunctor.map_comp]
  dsimp only [strictBETotJointSourceAugmentationInput, strictBETotJointSourceNativeDomain]
  simp only [Category.assoc]
  rw [← nerveOppositeIso_inv_naturality_assoc (strictBETotJointSourceFrameEvaluation A)]
  rw [← Category.assoc]
  have hn : nerveMap (strictBETotJointSourceParameterIndex A) ≫
      nerveMap (strictBETotJointSourceFrameEvaluation A).op =
        nerveMap (strictBETotJointSourceParameterIndex A ⋙
          (strictBETotJointSourceFrameEvaluation A).op) := rfl
  rw [hn, strictBETotJointSourceParameterIndex_evaluation]

/-- 同じ元の全augmentationの定値端は、元の試験対象の全射影へ戻る。 -/
theorem strictBETotJointSourceAugmentationInput_constant :
    strictBETotJointSourceAugmentationInput A ≫
      SSet.opFunctor.map (nerveMap (strictBETotJointSourceFrameConstant A) ≫
        strictBETotModelSource A) = strictBETotJointSourceOriginalNativeDomain A := by
  rw [SSet.opFunctor.map_comp]
  dsimp only [strictBETotJointSourceAugmentationInput, strictBETotJointSourceOriginalNativeDomain]
  simp only [Category.assoc]
  rw [← nerveOppositeIso_inv_naturality_assoc (strictBETotJointSourceFrameConstant A)]
  rw [← Category.assoc]
  have hn : nerveMap (strictBETotJointSourceParameterIndex A) ≫
      nerveMap (strictBETotJointSourceFrameConstant A).op =
        nerveMap (strictBETotJointSourceParameterIndex A ⋙
          (strictBETotJointSourceFrameConstant A).op) := rfl
  rw [hn, strictBETotJointSourceParameterIndex_constant]

/-- 元の全augmentationの同じ一つの同型を全実射の始域へ引き戻した比較。 -/
def strictBETotJointSourceAugmentationDomainIso :
    FunctorIso (strictBETotJointSourceNativeDomain A)
      (strictBETotJointSourceOriginalNativeDomain A) := by
  have h := (strictBETotJointSourceFrameAugmentationIso A).op.precomp
    (strictBETotJointSourceAugmentationInput A)
  rw [strictBETotJointSourceAugmentationInput_evaluation,
    strictBETotJointSourceAugmentationInput_constant] at h
  exact h
end SerrePositivity.EInfinity.BarrattEccles
