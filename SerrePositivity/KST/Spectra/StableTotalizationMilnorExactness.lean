module

public import SerrePositivity.KST.Spectra.StableTotalizationMilnorKernel
public import SerrePositivity.KST.Spectra.PartialTotalizationMilnorExactness

/-!
概要：BF の全整数次数の Milnor 単射と像の完全性。
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

/-- 次次数の lim¹ から BF の整数次数の群への Milnor 単射。 -/
def limOneBoundary :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (D ⋙ KanSequence.levelEvaluation k) n).right
        (r + 1) (stage (D ⋙ KanSequence.levelEvaluation k) n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step (D ⋙ KanSequence.levelEvaluation k) n)) →
      OmegaSpectrum.homotopyGroup (KanSequence.totalizationSpectrum D hD hΩ) j := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  intro a
  exact ((kernelLimOneEquiv D hD hΩ j k r hk).symm a).val

/-- Milnor 単射は標準基点を保つ。 -/
@[simp]
lemma limOneBoundary_point :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    limOneBoundary D hD hΩ j k r hk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) = 1 := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  unfold limOneBoundary
  rw [kernelLimOneEquiv_symm_point]
  rfl

/-- BF の整数次数の Milnor 境界は単射。 -/
lemma limOneBoundary_injective :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    Function.Injective (limOneBoundary D hD hΩ j k r hk) := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  exact Subtype.val_injective.comp (kernelLimOneEquiv D hD hΩ j k r hk).symm.injective

/-- 比較と Milnor 単射の合成は単位元。 -/
@[simp]
lemma comparison_limOneBoundary :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    ∀ a :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (D ⋙ KanSequence.levelEvaluation k) n).right
        (r + 1) (stage (D ⋙ KanSequence.levelEvaluation k) n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step (D ⋙ KanSequence.levelEvaluation k) n)),
      comparison D hD hΩ j k r hk (limOneBoundary D hD hΩ j k r hk a) = 1 := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  intro a
  exact ((kernelLimOneEquiv D hD hΩ j k r hk).symm a).property

/-- BF 整数次数の Milnor 単射の像は実際の骨格比較の核。 -/
lemma limOneBoundary_range :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    Set.range (limOneBoundary D hD hΩ j k r hk) = (comparison D hD hΩ j k r hk).ker := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact comparison_limOneBoundary D hD hΩ j k r hk a
  · intro hb
    refine ⟨kernelLimOneEquiv D hD hΩ j k r hk ⟨b, hb⟩, ?_⟩
    unfold limOneBoundary
    rw [Equiv.symm_apply_apply]

end
end SerrePositivity.KST.Spectra.TotalizationMilnor
