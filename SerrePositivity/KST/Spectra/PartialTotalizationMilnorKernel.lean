module

public import SerrePositivity.KST.Spectra.PartialTotalizationMilnorComparison
public import SerrePositivity.KST.Spectra.MonoidKernelTransport

/-!
概要：通常 Tot の実際の比較の核と、部分 Tot の次次数の lim¹ の基点を保つ全単射。
方針：基点を保つ極限同型による核の群同型を、具体的な塔の障害写像へ合成する。
規約：順写像は具体的な塔へ移した実際の核の元の障害。
使われ方：Goerss–Jardine VIII §1。通常 Tot の Milnor 完全列の核の界面。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.PartialTotalizationTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : CosimplicialObject PointedSimplicialSet.{u})
  (hX : reedyRight simplex J.rlp (terminal.from (X ⋙ PointedSimplicialSet.forget)))

/-- 通常 Tot の比較の核を、具体的な塔の比較の核へ移す群同型。 -/
def kernelTowerEquiv (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    (groupComparison X hX r).ker ≃*
      (PointedFibrationTower.limitGroupComparison (stage X) (step X) r).ker := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  exact MonoidKernelTransport.precomp
    (PointedFibrationTower.limitGroupComparison (stage X) (step X) r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r (limitIso X) (limitIso_basepoint X))

/-- 通常 Tot の比較の核と、実際の部分 Tot の塔の lim¹ の全単射。 -/
def kernelLimOneEquiv (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    (groupComparison X hX r).ker ≃
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
        (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage X n).right (r + 1) (stage X n).basepoint)
        (fun n ↦ pointedGroupMap (r + 1) (step X n)) := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  exact (kernelTowerEquiv X hX r).toEquiv.trans
    (PointedFibrationTower.kernelLimOneEquiv (stage X) (step X) r)

/-- 通常 Tot の核の全単射は標準基点を保つ。 -/
@[simp]
lemma kernelLimOneEquiv_one (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    kernelLimOneEquiv X hX r 1 = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  change PointedFibrationTower.kernelLimOneEquiv (stage X) (step X) r
    (kernelTowerEquiv X hX r 1) = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _
  rw [map_one, PointedFibrationTower.kernelLimOneEquiv_one]

/-- 逆写像も lim¹ の基点を単位元へ送る。 -/
@[simp]
lemma kernelLimOneEquiv_symm_point (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    (kernelLimOneEquiv X hX r).symm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) = 1 := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  apply (kernelLimOneEquiv X hX r).injective
  rw [Equiv.apply_symm_apply, kernelLimOneEquiv_one]

end
end SerrePositivity.KST.Spectra.PartialTotalizationTower
