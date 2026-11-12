module

public import SerrePositivity.KST.Spectra.TowerKernelObstruction

/-!
概要：各段で零ホモトピックな整合する球面から、極限の比較の核の元を構成する。
方針：球面を極限へ組み立て、射影公式で元の零ホモトピーの差の障害を回収する。
規約：極限での零ホモトピーは要求しない。各段の零ホモトピーだけを使う。
使われ方：Goerss–Jardine VIII §1。核から lim¹ への障害写像の全射性。
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

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ)
  (s : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint)
  (hs : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
    (s (n + 1)) = s n)
  (R : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)))

include R in
/-- 各段の零ホモトピーがあれば、組み立てた極限の球面は比較の核に属する。 -/
lemma limitSimplex_mem_kernel :
    limitGroupComparison X p r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (limitSimplex X p r s hs)) = 1 := by
  apply (limitGroupComparison_eq_one_iff X p r _).2
  intro n
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map _ rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (limitSimplex X p r s hs)) = 1
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, limitSimplex_projection]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (R n)).symm

omit [∀ n, Fibration (p n).right] in
/-- 整合する球面の族の等式による同定は、零ホモトピーの障害を保つ。 -/
lemma nullHomotopyObstruction_eq_cast
    (t : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint)
    (ht : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
      (t (n + 1)) = t n) (he : s = t) :
    nullHomotopyObstruction X p r t ht (he ▸ R) =
      nullHomotopyObstruction X p r s hs R := by
  cases he
  rfl

/-- 極限へ組み立てた核の元の障害は、元の零ホモトピーの隣接差で計算できる。 -/
lemma kernelObstruction_limitSimplex :
    kernelObstruction X p r
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (limitSimplex X p r s hs), limitSimplex_mem_kernel X p r s hs R⟩ =
    nullHomotopyObstruction X p r s hs R := by
  rw [kernelObstruction_mk]
  have he : s = projectedSimplex X p r (limitSimplex X p r s hs) := by
    funext n
    exact (limitSimplex_projection X p r s hs n).symm
  let R' : ∀ n, PtSimplex.RelStruct .const
      (projectedSimplex X p r (limitSimplex X p r s hs) n) (Fin.last (r + 1)) := he ▸ R
  rw [kernelRepresentativeObstruction_eq X p r _ _ R']
  exact nullHomotopyObstruction_eq_cast X p r s hs R _ _ he

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
