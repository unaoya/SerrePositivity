module

public import SerrePositivity.KST.Spectra.StableTotalizationEvaluation
public import SerrePositivity.KST.Spectra.PartialTotalizationMilnorExactness

/-!
概要：通常 Tot の BF 模型の整数次数から、実際の部分 Tot の群の逆極限への Milnor 比較。
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

/-- 任意の整数次数の群から実際の部分 Tot の群の逆極限への比較。 -/
def comparison :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    OmegaSpectrum.homotopyGroup (KanSequence.totalizationSpectrum D hD hΩ) j →*
      PointedFibrationTower.compatibleGroup
        (stage (D ⋙ KanSequence.levelEvaluation k))
        (step (D ⋙ KanSequence.levelEvaluation k)) r := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  exact (groupComparison _ (hD k) r).comp (evaluation D hD hΩ j k r hk).toMonoidHom

/-- 整数次数の比較の各座標は BF 射影後の実際の骨格制限。 -/
lemma comparison_apply (n : ℕ) :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    ∀ a : OmegaSpectrum.homotopyGroup (KanSequence.totalizationSpectrum D hD hΩ) j,
      (comparison D hD hΩ j k r hk a).val n =
        pointedGroupMap r (restriction (D ⋙ KanSequence.levelEvaluation k) n)
          (evaluation D hD hΩ j k r hk a) := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  intro a
  exact groupComparison_apply _ (hD k) r n _

/-- BF の任意の整数次数の Milnor 比較は全射。 -/
lemma comparison_surjective :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    letI : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ stage_kanComplex _ (hD k) n
    letI : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
      fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
    Function.Surjective (comparison D hD hΩ j k r hk) := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let : ∀ n, KanComplex (stage (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ stage_kanComplex _ (hD k) n
  let : ∀ n, Fibration (step (D ⋙ KanSequence.levelEvaluation k) n).right :=
    fun n ↦ map_fibration _ (hD k) (Nat.le_succ n)
  exact (groupComparison_surjective _ (hD k) r).comp (evaluation D hD hΩ j k r hk).surjective

end
end SerrePositivity.KST.Spectra.TotalizationMilnor
