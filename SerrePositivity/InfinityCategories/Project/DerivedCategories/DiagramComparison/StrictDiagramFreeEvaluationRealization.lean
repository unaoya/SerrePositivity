module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationFrames
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowRealization
public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsCopowerRealization
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality

/-!
概要：元の自由arrow実現を評価し、要素圏上の指定実現へ同定する。
方針：評価との交換、評価したframeの同定、余積実現の要素圏表示を合成する。
使われ方：HTT 4.2.4.4、RR02(a)の元の増大射の値ごとの比較。
規約：BK重みは元の射影で制限したまま。弱同値性は別途示す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance freeEvaluationRealization_hasColimits : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance freeEvaluationRealization_hasCoproducts : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape
local instance freeEvaluationRealization_hasProducts : ∀ (i j : strictDiagramIndex d),
    HasProductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasLimitsOfShape
local instance freeEvaluationRealization_modelCategory : HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

/-- 指定した自由arrow実現の評価値を、そのまま要素圏の実現として表す。 -/
def strictDiagramFreeEvaluationRealizationIso (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :
    (strictDiagramFreeArrowRealization A d X).obj k ≅
      (FrameWeightRealization.functor (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elements
        (Functor.Elements.π (strictDiagramFreeEvaluationLiftedWeight d k) ⋙
          strictDiagramFreeEvaluationBase A d X)).obj
        ((Functor.Elements.π (strictDiagramFreeEvaluationLiftedWeight d k)).op ⋙
          bousfieldKanWeight ((StrictDiagramArrowElements.{u} d)ᵒᵖ)ᵒᵖ) :=
  (FrameWeightRealization.postIso (StrictDiagramArrowElements.{u} d)ᵒᵖ
    (evaluationAdjunctionLeft (Complex A) k) (strictDiagramFreeArrowFrame A d X)).app _ ≪≫
  ((FrameWeightRealization.family (StrictDiagramArrowElements.{u} d)ᵒᵖ).mapIso
    (strictDiagramFreeEvaluationFramesIso A d X k)).app _ ≪≫
  ElementsCopower.realizationIso (strictDiagramFreeEvaluationLiftedWeight d k)
    (strictDiagramFreeEvaluationBase A d X) _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
