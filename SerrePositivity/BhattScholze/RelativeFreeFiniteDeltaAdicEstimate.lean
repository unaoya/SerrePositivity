module

public import SerrePositivity.BhattScholze.RelativeFreeFiniteDeltaStepIdentities
public import SerrePositivity.BhattScholze.DeltaAdicEstimate
public import SerrePositivity.BhattScholze.RelativeDeltaEstimate
public import Mathlib.RingTheory.Ideal.Maps

/-! # 異なる有限段の間のδ計算のイデアル冪評価

次段イデアルJと初期包含の逆像について、有限δ計算で失う冪を追う。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 次段のJがpを含むなら、逆像のm+1乗の有限δ像はJのm乗に入る。 -/
theorem relativeFreeFiniteDeltaStep_mem_pow (D : DeltaStructure p A)
    (J : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hp : (p : MvPolynomial (σ × Fin (N + 2)) A) ∈ J)
    (m : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A)
    (hf : f ∈ (J.comap (relativeFreeFiniteStepInclusion N σ)) ^ (m + 1)) :
    relativeFreeFiniteDeltaStep N σ D f ∈ J ^ m := by
  exact wittTwoLift_delta_mem_pow (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) J hp m f hf

/-- 逆像のm+1乗に属す摂動による有限δ像の変化はJのm乗に入る。 -/
theorem relativeFreeFiniteDeltaStep_add_sub_mem_pow (D : DeltaStructure p A)
    (J : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hp : (p : MvPolynomial (σ × Fin (N + 2)) A) ∈ J)
    (m : ℕ) (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hg : g ∈ (J.comap (relativeFreeFiniteStepInclusion N σ)) ^ (m + 1)) :
    relativeFreeFiniteDeltaStep N σ D (f + g) - relativeFreeFiniteDeltaStep N σ D f ∈
      J ^ m := by
  exact wittTwoLift_delta_add_sub_mem_pow (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) J hp m f g hg

/-- 二代表元が逆像のm+1乗まで一致すれば有限δ像はJのm乗まで一致する。 -/
theorem relativeFreeFiniteDeltaStep_sub_mem_pow (D : DeltaStructure p A)
    (J : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hp : (p : MvPolynomial (σ × Fin (N + 2)) A) ∈ J)
    (m : ℕ) (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hfg : f - g ∈ (J.comap (relativeFreeFiniteStepInclusion N σ)) ^ (m + 1)) :
    relativeFreeFiniteDeltaStep N σ D f - relativeFreeFiniteDeltaStep N σ D g ∈ J ^ m := by
  exact wittTwoLift_delta_sub_mem_pow (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) J hp m f g hfg

end SerrePositivity.BhattScholze
