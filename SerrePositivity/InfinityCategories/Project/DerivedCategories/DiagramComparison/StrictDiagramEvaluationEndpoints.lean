module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramEvaluationFactorization

/-!
概要：同じ宇宙の局所化評価を、任意のパラメーターと指定添字で照合する。
方針：元の全関手同型を前合成・後合成し、通常評価の等式を使う。
規約：添字はΔ・Δᵒᵖのみ。パラメーターはSSet.{u + 1}、値は指定された同じD(A)。
使われ方：3b-3 R7、図式射・固定端点の表示を変更せずに比較を使用する入口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)

/-- 元のstrict図式の任意の全パラメーター族で、同じ評価比較を使用できる。 -/
def strictDiagramDerivedEvaluation_parameterIso {P : SSet.{u + 1}}
    (F : P ⟶ strictComplexDiagramNerve A d) :
    FunctorIso
      (F ≫ strictDiagramLocalization A d ≫ strictDiagramDerivedEvaluation A d)
      (F ≫ strictComplexDiagramFamily A d) :=
  (strictDiagramDerivedEvaluation_factor A d).precomp F

/-- 指定添字での評価の比較。各辺の両端を含む全パラメーターを同時に保つ。 -/
def strictDiagramDerivedEvaluation_endpointIso {P : SSet.{u + 1}}
    (F : P ⟶ strictComplexDiagramNerve A d) (j : strictDiagramIndex d) :
    FunctorIso
      (F ≫ strictDiagramLocalization A d ≫ strictDiagramDerivedEvaluation A d ≫
        evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ j)))
      (F ≫ nerveMap ((CategoryTheory.evaluation (strictDiagramIndex d) (Complex A)).obj j) ≫
        complexDerivedEvaluation A) := by
  have e := ((strictDiagramDerivedEvaluation_factor A d).postcomp
    (evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ j)))).precomp F
  rw [strictComplexDiagramFamily_evaluation] at e
  exact e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
