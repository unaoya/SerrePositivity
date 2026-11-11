module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationNaturalTransportComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionDiagram

/-!
概要：底上の可換三角形の切断制限と頂点評価の比較。
方針：実際の底の可換性に沿う終点の輸送を記録して豊穣比較の合成則へ戻す。
規約：比較の辺と端点の同定を変更しない。
使われ方：共同降下の自然性を両端の fiber 評価へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：可換三角形で制限した切断の評価点は元の図式の像の評価点。
方針：三角形の可換性を指定頂点で評価する。
規約：終点の同定の向きを固定する。
使われ方：fiber 評価の頂点を輸送する等式。 -/
lemma overPreEvaluationVertex {A D B : SSet.{u}} (a : A ⟶ B) (d : D ⟶ B)
    (i : D ⟶ A) (h : i ≫ a = d) (v : D _⦋0⦌) :
    d.app (Opposite.op ⦋0⦌) v = a.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) v) := by
  rw [← h]
  rfl

/-- 概要：底上の切断制限と頂点評価は全対象の関手空間で可換。
方針：可換三角形を合成表示へ戻して、既存の豊穣比較の合成則を適用する。
規約：fiber 評価の終点は可換性から生じる等式で輸送する。
使われ方：降下同型の自然性を既存 transport の評価公式へ接続する。 -/
lemma relativeFunctorOverPreComparisonEdge_evaluate {A D B : SSet.{u}}
    (a : A ⟶ B) (d : D ⟶ B) (i : D ⟶ A) (h : i ≫ a = d) (v : D _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonEdge
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeFunctorOverPreComparison (Over.homMk i h : Over.mk d ⟶ Over.mk a))) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge d v) ≫
      eqToHom (congrArg (fun b ↦ HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b)))
          (overPreEvaluationVertex a d i h v)) =
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge a (i.app (Opposite.op ⦋0⦌) v)) := by
  subst d
  simp only [eqToHom_refl, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPrecompositionComparisonEdge_evaluate a i v

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
