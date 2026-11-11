module

public import SerrePositivity.KST.Spectra.TowerKernelObstructionInjective
public import SerrePositivity.KST.Spectra.TowerKernelObstructionSurjective

/-!
概要：Kan fibration の塔の比較の核と非可換 lim¹ の基点を保つ全単射。
方針：実際の障害写像の単射性と全射性を合わせ、逆写像と基点の公式を得る。
規約：全単射の順写像は既存の kernelObstruction そのもの。
使われ方：Goerss–Jardine VIII §1。Milnor の核と lim¹ の同定。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra.PointedFibrationTower
noncomputable section

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ)

/-- 塔の比較の核と、次のホモトピー群の塔の lim¹ の基点を保つ全単射。 -/
def kernelLimOneEquiv :
    (limitGroupComparison X p r).ker ≃
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n)) :=
  Equiv.ofBijective (kernelObstruction X p r)
    ⟨kernelObstruction_injective X p r, kernelObstruction_surjective X p r⟩

/-- 全単射の順写像は選び直した比較でなく実際の障害写像。 -/
@[simp]
lemma kernelLimOneEquiv_apply (b : (limitGroupComparison X p r).ker) :
    kernelLimOneEquiv X p r b = kernelObstruction X p r b := rfl

/-- 全単射は核の単位元を lim¹ の基点へ送る。 -/
@[simp]
lemma kernelLimOneEquiv_one :
    kernelLimOneEquiv X p r 1 = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ :=
  kernelObstruction_one X p r

/-- 全単射の逆も基点を保つ。 -/
@[simp]
lemma kernelLimOneEquiv_symm_point :
    (kernelLimOneEquiv X p r).symm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) = 1 := by
  apply (kernelLimOneEquiv X p r).injective
  rw [Equiv.apply_symm_apply, kernelLimOneEquiv_one]

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
