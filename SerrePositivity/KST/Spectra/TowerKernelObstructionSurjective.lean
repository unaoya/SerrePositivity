module

public import SerrePositivity.KST.Spectra.TowerKernelRealization
public import SerrePositivity.KST.Spectra.TowerDifferenceRealization

/-!
概要：Kan fibration の塔の比較の核から非可換 lim¹ への障害写像は全射。
方針：任意の軌道の代表を隣接差の族で実現し、球面を極限へ組み立てて障害を回収する。
規約：全射性を実際の球面と零ホモトピーから証明する。単射性は別工程。
使われ方：Goerss–Jardine VIII §1。Milnor の核と lim¹ の比較。
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

/-- 任意の非可換 lim¹ の元は、極限の比較の核の実際の球面から得られる。 -/
theorem kernelObstruction_surjective
    (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
    [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ) :
    Function.Surjective (kernelObstruction X p r) := by
  intro b
  obtain ⟨a, rfl⟩ := Quotient.exists_rep b
  obtain ⟨s, hs, R, hR⟩ := exists_nullHomotopyDifferenceFamily X p r a
  refine ⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (limitSimplex X p r s hs),
    limitSimplex_mem_kernel X p r s hs R⟩, ?_⟩
  rw [kernelObstruction_limitSimplex]
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk _ _ (nullHomotopyDifferenceFamily X p r s hs R) = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk _ _ a
  rw [hR]

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
