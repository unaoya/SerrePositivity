module

public import SerrePositivity.KST.Spectra.TowerHomotopyComparison

/-!
概要：塔で厳密に整合する相対ホモトピーを極限の相対ホモトピーへ組み立てる。
方針：RelStruct の単体を整合族の極限へ持ち上げ、全ての面を射影後に計算する。
規約：段ごとの零ホモトピーが自動的に整合するとは主張しない。
使われ方：Goerss–Jardine VIII §1。比較の核と lim¹ の障害の解析。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.PointedFibrationTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n) (r : ℕ)
    (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)).PtSimplex
      (r + 1) (limitBasepoint X p))
    (h : ∀ n, PtSimplex.RelStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n) rfl s)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n) rfl t)
      (Fin.last (r + 1)))
    (hc : ∀ n, (h (n + 1)).map ≫ (p n).right = (h n).map)

/-- 厳密に整合する相対ホモトピーの単体は極限での相対ホモトピーを与える。 -/
def limitRelStruct : PtSimplex.RelStruct s t (Fin.last (r + 1)) where
  map := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift _ _ (fun n ↦ (h n).map) hc
  δ_castSucc_map := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext (fun n ↦ (X n).right) (fun n ↦ (p n).right)
    intro n
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection]
    exact (h n).δ_castSucc_map
  δ_succ_map := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext (fun n ↦ (X n).right) (fun n ↦ (p n).right)
    intro n
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection]
    exact (h n).δ_succ_map
  δ_map_of_lt j hj := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext (fun n ↦ (X n).right) (fun n ↦ (p n).right)
    intro n
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection, const_comp]
    exact (h n).δ_map_of_lt j hj
  δ_map_of_gt j hj := (not_lt_of_ge (Fin.le_last j) hj).elim

include h hc in
/-- 整合する相対ホモトピーを持つ二つの極限の代表は、極限で同じ類になる。 -/
theorem class_eq_of_compatible_relations [∀ n, KanComplex (X n).right]
    [∀ n, Fibration (p n).right] : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (limitRelStruct X p r s t h hc)

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
