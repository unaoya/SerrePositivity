module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeLeftFibrationHomNative
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningAllBasesEvaluation

/-!
概要：一点始域の相対 Hom の全評価関手と、元の left fibration の頂点 fiber 評価を比較する。
方針：F1 の相対切断の評価比較を恒等射に適用し、元の底の指定頂点を回収する。
規約：対象ごとの同値ではなく、全 left fibrations 上の coherent な関手同型。
使われ方：元の底上の strict filtered 全余錐の native な普遍性の検出。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 指定頂点への一点図式からの相対 Hom は、同じ頂点の全 fiber 評価と関手同型。 -/
def leftFibrationPointEvaluationIso {B : SSet.{u}} (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation (Over.mk (SSet.yonedaEquiv.symm b)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b) := by
  have hb : (SSet.yonedaEquiv.symm b).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = b := by
    change B.map (stdSimplex.obj₀Equiv.symm (0 : Fin 1)).down.op b = b
    have hh : (stdSimplex.obj₀Equiv.symm (0 : Fin 1)).down = 𝟙 ⦋0⦌ :=
      @Subsingleton.elim ((⦋0⦌ : SimplexCategory) ⟶ ⦋0⦌) inferInstance _ _
    rw [hh, op_id, CategoryTheory.Functor.map_id_apply]
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonIso
    (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.id_mem _)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation (Over.mk (SSet.yonedaEquiv.symm b)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation
      ((SSet.yonedaEquiv.symm b).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))) at h
  simpa only [hb] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
