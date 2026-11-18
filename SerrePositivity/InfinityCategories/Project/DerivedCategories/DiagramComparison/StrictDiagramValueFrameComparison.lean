module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramEvaluatedAugmentation
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FixedQuillenFrameComparison

/-!
概要：評価source frameと標準複体frameの比較を、全添字に自然なcospanで与える。
方針：既存のFrameOverFunctorを同じ増大射に適用し、両脚の値での同値性を使う。
規約：比較は二変数の自然変換であり、coherent endの同値性は別の主張。
使われ方：Hovey §5.4、HTT 4.2.4.4のRR02の値の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
local instance valueFrameModel : ModelCategory (Complex A) := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
local instance valueFrameInitial : HasInitial (Complex A) :=
  (isZero_zero (Complex A)).isInitial.hasInitial

/-- 標準複体frameの関手的分解を、元の生成モデルから固定する。 -/
def strictDiagramValueCofFactorization :
    MorphismProperty.FunctorialFactorizationData
      (cofibrations (Complex A)) (trivialFibrations (Complex A)) := by
  haveI := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated A
  haveI := hasFunctorialFactorization_cofibration_trivialFibration
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A)
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A)
  exact MorphismProperty.functorialFactorizationData _ _

variable (d : StrictDiagramDirection)

/-- 同じ評価増大射と標準増大射の上の、全添字に自然な共通frame。 -/
def strictDiagramCommonValueFrame (X : StrictComplexDiagram A d) :
    strictDiagramIndex d ⥤ (SimplexCategory ⥤ Complex A) :=
  FrameOverFunctor.commonObj (strictDiagramValueCofFactorization A)
    (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)) X
    (strictDiagramEvaluatedSourceFrames A d X) (strictDiagramEvaluatedAugmentation A d X)

/-- 標準値frameのHomから共通frameのHomへの、二変数に自然な比較。 -/
def strictDiagramValueFrameHomLeft (X : StrictComplexDiagram A d) :
    FrameOverFunctor.hom
      (X ⋙ (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)).obj) ⟶
    FrameOverFunctor.hom (strictDiagramCommonValueFrame A d X) :=
  FrameOverFunctor.homLeft (strictDiagramValueCofFactorization A)
    (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)) X
    (strictDiagramEvaluatedSourceFrames A d X) (strictDiagramEvaluatedAugmentation A d X)

/-- 元の評価frameのHomから同じ共通frameのHomへの、二変数に自然な比較。 -/
def strictDiagramValueFrameHomRight (X : StrictComplexDiagram A d) :
    FrameOverFunctor.hom (strictDiagramEvaluatedSourceFrames A d X) ⟶
    FrameOverFunctor.hom (strictDiagramCommonValueFrame A d X) :=
  FrameOverFunctor.homRight (strictDiagramValueCofFactorization A)
    (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)) X
    (strictDiagramEvaluatedSourceFrames A d X) (strictDiagramEvaluatedAugmentation A d X)

/-- 左脚は、同じfibrant標的の各値でホモトピー同値。 -/
lemma strictDiagramValueFrameHomLeft_equivalence (X Y : StrictComplexDiagram A d)
    (i : (strictDiagramIndex d)ᵒᵖ) (j : strictDiagramIndex d) :
    IsSimplicialHomotopyEquivalence
      (((strictDiagramValueFrameHomLeft A d X).app i).app
        ((strictDiagramFibrantTarget A d Y).obj j)) := by
  haveI := strictDiagramFibrantTarget_obj_isFibrant A d Y j
  exact fixedFrameOverFunctor_homLeft_homotopyEquivalence
    (strictDiagramValueCofFactorization A)
    (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)) X
    (strictDiagramEvaluatedSourceFrames A d X) (strictDiagramEvaluatedAugmentation A d X)
    (strictDiagramEvaluatedAugmentation_weak A d X) i _

/-- 右脚も、指定した評価frameのcofibrancyから各値でホモトピー同値。 -/
lemma strictDiagramValueFrameHomRight_equivalence (X Y : StrictComplexDiagram A d)
    (i : (strictDiagramIndex d)ᵒᵖ) (j : strictDiagramIndex d) :
    IsSimplicialHomotopyEquivalence
      (((strictDiagramValueFrameHomRight A d X).app i).app
        ((strictDiagramFibrantTarget A d Y).obj j)) := by
  haveI := strictDiagramFibrantTarget_obj_isFibrant A d Y j
  exact fixedFrameOverFunctor_homRight_homotopyEquivalence
    (strictDiagramValueCofFactorization A)
    (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)) X
    (strictDiagramEvaluatedSourceFrames A d X) (strictDiagramEvaluatedAugmentation A d X)
    (strictDiagramEvaluatedAugmentation_weak A d X)
    (strictDiagramEvaluatedSourceFrame_cofibrant A d X)
    (strictDiagramEvaluatedSourceFrame_homotopicallyConstant A d X) i _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
