module

public import SerrePositivity.BhattScholze.RelativeFreeFiniteDeltaStepIdentities
public import SerrePositivity.BhattScholze.DeltaAdditionCarryProduct

/-! # 有限δ計算の減算誤差の平方所属

包含像が消えるイデアルの二乗まで、有限δ計算は符号・減算を保つ。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 有限δ計算の符号の誤差は、入力の包含像を含むイデアルの二乗に属する。 -/
theorem relativeFreeFiniteDeltaStep_neg_error_mem_square (D : DeltaStructure p A)
    (I : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (f : MvPolynomial (σ × Fin (N + 1)) A)
    (hf : relativeFreeFiniteStepInclusion N σ f ∈ I) :
    relativeFreeFiniteDeltaStep N σ D (-f) + relativeFreeFiniteDeltaStep N σ D f ∈ I ^ 2 := by
  have hn : relativeFreeFiniteStepInclusion N σ (-f) ∈ I := by
    rw [map_neg]
    exact I.neg_mem hf
  have hc := wittAdditionCarry_mem_square (p := p) I
    (relativeFreeFiniteStepInclusion N σ f) (relativeFreeFiniteStepInclusion N σ (-f)) hf hn
  have he := relativeFreeFiniteDeltaStep_add N σ D f (-f)
  rw [add_neg_cancel, relativeFreeFiniteDeltaStep_zero] at he
  have herr : relativeFreeFiniteDeltaStep N σ D (-f) + relativeFreeFiniteDeltaStep N σ D f =
      -((WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ f) +
        WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ (-f))).coeff 1) := by
    rw [add_comm (relativeFreeFiniteDeltaStep N σ D (-f))
      (relativeFreeFiniteDeltaStep N σ D f)]
    exact eq_neg_of_add_eq_zero_left he.symm
  rw [herr]
  exact (I ^ 2).neg_mem hc

/-- 二つの包含像が属すイデアルの二乗まで、有限δ計算は減算を保つ。 -/
theorem relativeFreeFiniteDeltaStep_sub_error_mem_square (D : DeltaStructure p A)
    (I : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hf : relativeFreeFiniteStepInclusion N σ f ∈ I)
    (hg : relativeFreeFiniteStepInclusion N σ g ∈ I) :
    relativeFreeFiniteDeltaStep N σ D (f - g) -
      (relativeFreeFiniteDeltaStep N σ D f - relativeFreeFiniteDeltaStep N σ D g) ∈ I ^ 2 := by
  have hn : relativeFreeFiniteStepInclusion N σ (-g) ∈ I := by
    rw [map_neg]
    exact I.neg_mem hg
  have hc := wittAdditionCarry_mem_square (p := p) I
    (relativeFreeFiniteStepInclusion N σ f) (relativeFreeFiniteStepInclusion N σ (-g)) hf hn
  have he := (I ^ 2).add_mem
    (relativeFreeFiniteDeltaStep_neg_error_mem_square N σ D I g hg) hc
  rw [sub_eq_add_neg f g, relativeFreeFiniteDeltaStep_add]
  convert he using 1
  ring

end SerrePositivity.BhattScholze
