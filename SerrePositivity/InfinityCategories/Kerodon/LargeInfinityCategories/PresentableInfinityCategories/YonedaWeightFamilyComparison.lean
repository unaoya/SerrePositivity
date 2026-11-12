module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.YonedaWeightLeftKan
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomWeightEvaluationFamily
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.F2PresentableSigmaHomWeightRestriction

/-!
概要：元の全 Yoneda 自然変換空間族と、元の全係数前層評価族を全自然同型で比較する。
方針：全前層 Yoneda 評価比較を元の全係数へ制限し、二変数交換で全族に戻す。
規約：全 C・全標的係数・元の Hom 係数関手を保持する。
使われ方：P_Σ 延長の二つの右 Kan 族の制限同型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 概要：元の全係数で制限した Yoneda Hom 関手の転置は、同じ全自然変換空間族そのもの。
方針：全前層 Yoneda 評価比較を元の全係数へ制限し、二変数交換で全族に戻す。
規約：全 C・全標的係数・元の Hom 係数関手を保持する。
使われ方：P_Σ 延長の二つの右 Kan 族の制限同型。 -/
lemma yonedaHomWeightFamily_transpose
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F₀) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap ((SSet.uliftFunctor.{u + 1, u}).obj C))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightFamily F₀ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transposeFunctorFamily_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightFamily]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily]
  erw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram_transpose]
  rw [Category.assoc]

/-- 概要：元の全 Yoneda 自然変換空間族は、全係数前層評価族と両変数で自然同型。
方針：全前層 Yoneda 評価比較を元の全係数へ制限し、二変数交換で全族に戻す。
規約：全 C・全標的係数・元の Hom 係数関手を保持する。
使われ方：P_Σ 延長の二つの右 Kan 族の制限同型。 -/
def yonedaHomWeightFamily_evaluationIso
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightFamily F₀) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homWeightEvaluationFamily F₀) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIso.transpose
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightDiagram_universeIso ((SSet.uliftFunctor.{u + 1, u}).obj C)).precomp
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F₀)))
  rw [yonedaHomWeightFamily_transpose] at e
  exact e

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
