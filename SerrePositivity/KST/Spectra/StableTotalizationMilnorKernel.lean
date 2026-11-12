module

public import SerrePositivity.KST.Spectra.StableTotalizationComparison
public import SerrePositivity.KST.Spectra.PartialTotalizationMilnorExactness

/-!
概要：通常 Tot の BF 模型の整数次数の Milnor 核と、次次数の部分 Tot の lim¹。
方針：十分高い通常 Tot の段への群同型で核を移し、実構成した lim¹ の障害へ合成する。
規約：各座標は BF 射影後の実際の骨格制限。j+k=r+1 を明示する。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。L9e の全整数次数の収束界面。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.TotalizationMilnor
noncomputable section
open PartialTotalizationTower
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (D : CosimplicialObject KanSequence.{u}) (hD : KanSequence.TotalizationReedy D)
  (hΩ : ∀ a, (D.obj a).OmegaCondition)
  (j : ℤ) (k r : ℕ) (hk : j + (k : ℤ) = (r + 1 : ℕ))

/-- BF 整数次数の比較の核と、元の通常 Tot の比較の核の群同型。 -/
def kernelOrdinaryEquiv :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    (comparison D hD hΩ j k r hk).ker ≃*
      (groupComparison (D ⋙ KanSequence.levelEvaluation k) (hD k) r).ker := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  exact MonoidKernelTransport.precomp (groupComparison _ (hD k) r)
    (evaluation D hD hΩ j k r hk)

/-- BF 整数次数の比較の核は、実際の骨格塔の次次数の lim¹ と全単射。 -/
def kernelLimOneEquiv :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    (comparison D hD hΩ j k r hk).ker ≃
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
        (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (D ⋙ KanSequence.levelEvaluation k) n).right
          (r + 1) (stage (D ⋙ KanSequence.levelEvaluation k) n).basepoint)
        (fun n ↦ pointedGroupMap (r + 1) (step (D ⋙ KanSequence.levelEvaluation k) n)) := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  exact (kernelOrdinaryEquiv D hD hΩ j k r hk).toEquiv.trans
    (PartialTotalizationTower.kernelLimOneEquiv _ (hD k) r)

/-- BF 整数次数の核の同定も標準基点を保つ。 -/
@[simp]
lemma kernelLimOneEquiv_one :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    kernelLimOneEquiv D hD hΩ j k r hk 1 = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  change PartialTotalizationTower.kernelLimOneEquiv _ (hD k) r
    (kernelOrdinaryEquiv D hD hΩ j k r hk 1) = _
  rw [map_one, PartialTotalizationTower.kernelLimOneEquiv_one]

/-- 核の全単射の逆も基点を保つ。 -/
@[simp]
lemma kernelLimOneEquiv_symm_point :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    (kernelLimOneEquiv D hD hΩ j k r hk).symm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) = 1 := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  apply (kernelLimOneEquiv D hD hΩ j k r hk).injective
  rw [Equiv.apply_symm_apply, kernelLimOneEquiv_one]

end
end SerrePositivity.KST.Spectra.TotalizationMilnor
