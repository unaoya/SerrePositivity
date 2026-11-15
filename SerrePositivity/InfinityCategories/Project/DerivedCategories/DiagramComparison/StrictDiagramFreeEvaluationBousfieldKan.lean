module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationRealization
public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsBousfieldKanWeight

/-!
概要：自由arrow実現の評価値を、要素圏上の指定BK実現として表す。
方針：評価実現同型に、要素射影の重み同型の逆の実現を合成する。
使われ方：HTT 4.2.4.4、RR02(a)の評価点での増大射の比較。
規約：同じ実現対象の同定であり、増大射の弱同値性は別途示す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance freeEvaluationBK_hasColimits : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance freeEvaluationBK_modelCategory :
    HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

/-- 評価実現同型を、要素圏自身の指定BK重みまで合成する。 -/
def strictDiagramFreeEvaluationBousfieldKanIso (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :
    (strictDiagramFreeArrowRealization A d X).obj k ≅
      (FrameWeightRealization.functor
        (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elements
        (Functor.Elements.π (strictDiagramFreeEvaluationLiftedWeight d k) ⋙
          strictDiagramFreeEvaluationBase A d X)).obj
        (bousfieldKanWeight (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elementsᵒᵖ) :=
  strictDiagramFreeEvaluationRealizationIso A d X k ≪≫
    (FrameWeightRealization.functor
      (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elements
      (Functor.Elements.π (strictDiagramFreeEvaluationLiftedWeight d k) ⋙
        strictDiagramFreeEvaluationBase A d X)).mapIso
      (ElementsUnderProjection.weightIso (strictDiagramFreeEvaluationLiftedWeight d k)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
