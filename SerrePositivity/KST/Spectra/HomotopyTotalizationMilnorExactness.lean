module

public import SerrePositivity.KST.Spectra.HomotopyTotalizationMilnorComparison

/-!
概要：既存 homotopyTotalization の全整数次数の Milnor 完全列と収束判定。
方針：実際の核と lim¹ の全単射の逆を包含し、完全性と全単射判定を得る。
規約：元の Ω 図式の Reedy 性は不要。比較の各座標と全射性を計算する。
使われ方：Goerss–Jardine VIII §1。任意の余単体 Ω 図式の Milnor 比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra.HomotopyTotalizationMilnor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open PartialTotalizationTower

variable (X : CosimplicialObject OmegaSpectrum.{u})
  (j : ℤ) (k r : ℕ) (hk : j + (k : ℤ) = (r + 1 : ℕ))

/-- 既存 homotopy Tot の Milnor 境界は実際の核の包含。 -/
def limOneBoundary :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (coefficients X k) n).right (r + 1)
        (stage (coefficients X k) n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step (coefficients X k) n)) →
      OmegaSpectrum.homotopyGroup (homotopyTotalization X) j := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  exact fun a ↦ ((kernelLimOneEquiv X j k r hk).symm a).val

/-- Milnor 境界は標準基点を保つ。 -/
@[simp]
lemma limOneBoundary_point :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    limOneBoundary X j k r hk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) = 1 := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  unfold limOneBoundary
  rw [kernelLimOneEquiv_symm_point]
  rfl

/-- 全整数次数の Milnor 境界は単射。 -/
lemma limOneBoundary_injective :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    Function.Injective (limOneBoundary X j k r hk) := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  exact Subtype.val_injective.comp (kernelLimOneEquiv X j k r hk).symm.injective

/-- Milnor 境界と比較の合成は単位元。 -/
@[simp]
lemma comparison_limOneBoundary :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    ∀ a : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (coefficients X k) n).right (r + 1)
        (stage (coefficients X k) n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step (coefficients X k) n)),
      comparison X j k r hk (limOneBoundary X j k r hk a) = 1 := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  intro a
  exact ((kernelLimOneEquiv X j k r hk).symm a).property

/-- 全整数次数の Milnor 境界の像は比較の核。 -/
lemma limOneBoundary_range :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    Set.range (limOneBoundary X j k r hk) = (comparison X j k r hk).ker := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact comparison_limOneBoundary X j k r hk a
  · intro hb
    refine ⟨kernelLimOneEquiv X j k r hk ⟨b, hb⟩, ?_⟩
    unfold limOneBoundary
    rw [Equiv.symm_apply_apply]

/-- 既存 homotopy Tot の整数次数の比較は lim¹ 消滅と同値に全単射。 -/
lemma comparison_bijective_iff :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    Function.Bijective (comparison X j k r hk) ↔ Subsingleton (
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (coefficients X k) n).right (r + 1)
        (stage (coefficients X k) n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step (coefficients X k) n))) := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  change Function.Bijective ((groupComparison (coefficients X k) (reedy X k) r) ∘
    (evaluation X j k r hk)) ↔ _
  rw [Function.Bijective.of_comp_iff _ (evaluation X j k r hk).bijective]
  exact groupComparison_bijective_iff (coefficients X k) (reedy X k) r

/-- 元の homotopy Tot も、実際の置換後の骨格塔の Mittag–Leffler 条件で収束する。 -/
lemma comparison_bijective_of_mittagLeffler :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (coefficients X k) n).right (r + 1)
        (stage (coefficients X k) n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step (coefficients X k) n)) →
    Function.Bijective (comparison X j k r hk) := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  intro hML
  exact (comparison_bijective_iff X j k r hk).2
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.subsingleton_of_mittagLeffler _ _ hML)

end
end SerrePositivity.KST.Spectra.HomotopyTotalizationMilnor
