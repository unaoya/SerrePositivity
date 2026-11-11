module

public import SerrePositivity.KST.Spectra.HomotopyTotalizationTower

/-!
概要：既存の homotopyTotalization の全整数次数の群から、実際の部分 Tot の群への比較。
方針：構成した通常 Tot の段評価を、元の骨格制限の比較へ合成する。
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

/-- 既存 homotopy Tot の整数次数から、実際の部分 Tot の群の逆極限への比較。 -/
def comparison :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    OmegaSpectrum.homotopyGroup (homotopyTotalization X) j →*
    PointedFibrationTower.compatibleGroup
      (stage (coefficients X k)) (step (coefficients X k)) r := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  exact (groupComparison (coefficients X k) (reedy X k) r).comp (evaluation X j k r hk).toMonoidHom

/-- 比較の各座標は選択した BF 比較の逆の後の実際の骨格制限。 -/
lemma comparison_apply (n : ℕ)
    (a : OmegaSpectrum.homotopyGroup (homotopyTotalization X) j) :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    (comparison X j k r hk a).val n =
      pointedGroupMap r (restriction (coefficients X k) n) (evaluation X j k r hk a) := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  exact groupComparison_apply (coefficients X k) (reedy X k) r n _

/-- 既存 homotopy Tot の全整数次数の Milnor 比較は全射。 -/
lemma comparison_surjective :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    Function.Surjective (comparison X j k r hk) := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  exact (groupComparison_surjective (coefficients X k) (reedy X k) r).comp
    (evaluation X j k r hk).surjective

/-- 元の homotopy Tot の核を置換した通常 Tot の核へ移す群同型。 -/
def kernelOrdinaryEquiv :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    (comparison X j k r hk).ker ≃*
    (groupComparison (coefficients X k) (reedy X k) r).ker := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  exact MonoidKernelTransport.precomp (groupComparison (coefficients X k) (reedy X k) r)
    (evaluation X j k r hk)

/-- 既存 homotopy Tot の比較の核と、部分 Tot の次次数の lim¹ の全単射。 -/
def kernelLimOneEquiv :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    (comparison X j k r hk).ker ≃
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage (coefficients X k) n).right (r + 1)
        (stage (coefficients X k) n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step (coefficients X k) n)) := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  exact (kernelOrdinaryEquiv X j k r hk).toEquiv.trans
    (PartialTotalizationTower.kernelLimOneEquiv (coefficients X k) (reedy X k) r)

/-- 核の全単射は lim¹ の標準基点を保つ。 -/
@[simp]
lemma kernelLimOneEquiv_one :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    kernelLimOneEquiv X j k r hk 1 = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  change PartialTotalizationTower.kernelLimOneEquiv (coefficients X k) (reedy X k) r
    (kernelOrdinaryEquiv X j k r hk 1) = _
  rw [map_one, PartialTotalizationTower.kernelLimOneEquiv_one]

/-- 核の全単射の逆も基点を保つ。 -/
@[simp]
lemma kernelLimOneEquiv_symm_point :
    letI := totalization_kanComplex X k
    letI : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
    letI : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
    (kernelLimOneEquiv X j k r hk).symm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) = 1 := by
  let := totalization_kanComplex X k
  let : ∀ n, KanComplex (stage (coefficients X k) n).right := stage_kanComplex X k
  let : ∀ n, HomotopicalAlgebra.Fibration (step (coefficients X k) n).right := step_fibration X k
  apply (kernelLimOneEquiv X j k r hk).injective
  rw [Equiv.apply_symm_apply, kernelLimOneEquiv_one]

end
end SerrePositivity.KST.Spectra.HomotopyTotalizationMilnor
