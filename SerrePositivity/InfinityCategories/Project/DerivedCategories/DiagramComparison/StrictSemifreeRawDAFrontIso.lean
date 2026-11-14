module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeProjectiveFront
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FullFamilyUncurryIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：元の全native余錐族のD(A)値の前面を、指定のstrict全評価へ比較する。
方針：検証した同じ射影的前面の等式と、既存の一点比較の単位を合成する。
規約：全パラメーターと全高次単体のFunctorIsoを返す。
使われ方：3b-3 R6 U31、同じ余錐のcartesian輸送への底の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- U31の底の比較：同じrawなD(A)値の前面と元の指定strict全評価の全関手同型。 -/
def strictSemifreeRawDAFrontIso :
    let P := nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ)
    let I := (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)
    FunctorIso
      ((P ◁ joinInl I (Δ[0] : SSet.{u + 1})) ≫
        (P ◁ (strictSemifreeJoinShapeIso A).hom) ≫ strictSemifreeRawDAJoinFamily A)
      (strictSemifreeEvaluation A SimplexCategoryᵒᵖ) := by
  dsimp only
  have hc := congrArg (fun f => f ≫ (projectivePointEquivalence A).hom)
    (strictSemifreeProjectiveFront A)
  have hg :
      (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁
        joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0]) ≫
      (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁
        (strictSemifreeJoinShapeIso A).hom) ≫ strictSemifreeRawDAJoinFamily A =
      strictDiagramEvaluation SimplexCategoryᵒᵖ (ClosedCategory A (Semifree A)) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Semifree A) ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          ((semifreePointConstant A).comp (dgSemifreeToProjective A PUnit.{1})) ≫
          (projectivePointEquivalence A).hom := by
    simpa only [strictSemifreeRawDAJoinFamily, Category.assoc] using hc
  rw [hg]
  have hu := (semifreeProjectivePointUnitIso A).precomp
    (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (semifreePointConstant A))
  rw [semifreePointConstant_equivalence] at hu
  have h := hu.precomp
    (strictDiagramEvaluation SimplexCategoryᵒᵖ (ClosedCategory A (Semifree A)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Semifree A))
  simpa only [Category.assoc, Category.comp_id, strictSemifreeEvaluation,
    SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using! h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
