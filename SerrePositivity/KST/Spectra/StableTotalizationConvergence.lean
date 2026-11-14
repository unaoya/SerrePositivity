module

public import SerrePositivity.KST.Spectra.StableTotalizationMilnorExactness
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TowerLimOneMittagLeffler

/-!
概要：BF 整数次数の Milnor 比較の全単射性と lim¹ 消滅、Mittag–Leffler による収束。
方針：十分高い通常 Tot の段への群同型を、元の骨格制限の比較準同型へ合成する。
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

/-- BF 整数次数の比較が全単射となる必要十分条件は次次数の lim¹ 消滅。 -/
lemma comparison_bijective_iff :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    Function.Bijective (comparison D hD hΩ j k r hk) ↔
      Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (D ⋙ KanSequence.levelEvaluation k) n).right
        (r + 1) (stage (D ⋙ KanSequence.levelEvaluation k) n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step (D ⋙ KanSequence.levelEvaluation k) n))) := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  change Function.Bijective ((groupComparison _ (hD k) r) ∘
    (evaluation D hD hΩ j k r hk)) ↔ _
  rw [Function.Bijective.of_comp_iff _ (evaluation D hD hΩ j k r hk).bijective]
  exact groupComparison_bijective_iff _ (hD k) r

/-- 次次数の実際の群の塔が Mittag–Leffler なら整数次数の比較は全単射。 -/
lemma comparison_bijective_of_mittagLeffler :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (D ⋙ KanSequence.levelEvaluation k) n).right
        (r + 1) (stage (D ⋙ KanSequence.levelEvaluation k) n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step (D ⋙ KanSequence.levelEvaluation k) n)) →
      Function.Bijective (comparison D hD hΩ j k r hk) := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  intro hML
  exact (comparison_bijective_iff D hD hΩ j k r hk).2
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.subsingleton_of_mittagLeffler _ _ hML)

/-- 実際の骨格塔の Mittag–Leffler 条件による全整数次数の収束同型。 -/
def groupEquivOfMittagLeffler :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (D ⋙ KanSequence.levelEvaluation k) n).right
        (r + 1) (stage (D ⋙ KanSequence.levelEvaluation k) n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step (D ⋙ KanSequence.levelEvaluation k) n)) →
      OmegaSpectrum.homotopyGroup (KanSequence.totalizationSpectrum D hD hΩ) j ≃*
        PointedFibrationTower.compatibleGroup
          (stage (D ⋙ KanSequence.levelEvaluation k))
          (step (D ⋙ KanSequence.levelEvaluation k)) r := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  intro hML
  exact MulEquiv.ofBijective (comparison D hD hΩ j k r hk)
    (comparison_bijective_of_mittagLeffler D hD hΩ j k r hk hML)

end
end SerrePositivity.KST.Spectra.TotalizationMilnor
