module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FibrationRepresentativeTransport
public import SerrePositivity.KST.Spectra.PointedGroupProduct

/-!
概要：Kan fibration の塔の整合するホモトピー類を、厳密に整合する代表で実現する。
方針：初段の代表を選び、各遷移で相対ホーンにより次の代表の射影を調整する。
規約：正次数の群。極限との比較や単射性はここでは主張しない。
使われ方：Goerss–Jardine VIII §1。Milnor 比較の全射性への代表の構成。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.PointedFibrationTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right]
  (r : ℕ) (a : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right r (X n).basepoint)
  (ha : ∀ n, pointedGroupMap r (p n) (a (n + 1)) = a n)

/-- 各段で指定した類を持つ代表を、前段の代表を固定して帰納的に選ぶ。 -/
def representatives : ∀ n, {s : (X n).right.PtSimplex (r + 1) (X n).basepoint //
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = a n}
  | 0 => ⟨Classical.choose (Quotient.exists_rep (a 0)),
      Classical.choose_spec (Quotient.exists_rep (a 0))⟩
  | n + 1 =>
    let prev := representatives n
    let hex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_representative_at (p n).right
      (X (n + 1)).basepoint (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (a (n + 1)) prev.val
      ((ha n).trans prev.property.symm)
    ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩

/-- 帰納的に選んだ代表の射影は、一つ前の代表そのもの。 -/
lemma representatives_comp (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
      (representatives X p r a ha (n + 1)).val = (representatives X p r a ha n).val := by
  dsimp only [representatives]
  exact (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_representative_at (p n).right
    (X (n + 1)).basepoint (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (a (n + 1))
    (representatives X p r a ha n).val
    ((ha n).trans (representatives X p r a ha n).property.symm))).2

include ha in
/-- 塔の整合する正次数ホモトピー類の族には、厳密に整合する代表の族がある。 -/
theorem exists_compatible_representatives :
    ∃ s : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint,
      (∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (s n) = a n) ∧
      ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (s (n + 1)) = s n :=
  ⟨fun n ↦ (representatives X p r a ha n).val,
    fun n ↦ (representatives X p r a ha n).property, representatives_comp X p r a ha⟩

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
