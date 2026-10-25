module

public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteDeltaPerturbation
public import Mathlib.RingTheory.Ideal.Operations

/-! # 有限δ計算の核の二乗に関する不変性

有限δ計算は異なる有限環の間の写像である。
通常射との合成について、初期包含の核の二乗に属す誤差を消す。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
variable (N : ℕ) (σ : Type v)

/-- 初期包含の核の二乗の元は、有限δ計算の後も通常射で消える。 -/
theorem relativeFreeFiniteDeltaStep_map_zero_of_mem_ker_square (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A)
    (hf : f ∈ (RingHom.ker (q.comp (relativeFreeFiniteStepInclusion N σ))) ^ 2) :
    q (relativeFreeFiniteDeltaStep N σ D f) = 0 := by
  let I := RingHom.ker (q.comp (relativeFreeFiniteStepInclusion N σ))
  have hf' : f ∈ I * I := by simpa only [I, pow_two] using hf
  have he : q (relativeFreeFiniteStepInclusion N σ f) = 0 ∧
      q (relativeFreeFiniteDeltaStep N σ D f) = 0 := by
    refine Submodule.mul_induction_on (C := fun z =>
      q (relativeFreeFiniteStepInclusion N σ z) = 0 ∧
        q (relativeFreeFiniteDeltaStep N σ D z) = 0) hf' ?_ ?_
    · intro a ha b hb
      change q (relativeFreeFiniteStepInclusion N σ a) = 0 at ha
      change q (relativeFreeFiniteStepInclusion N σ b) = 0 at hb
      constructor
      · rw [map_mul, map_mul, ha, zero_mul]
      · rw [relativeFreeFiniteDeltaStep_map_mul_of_prime_zero N σ D q hp,
          ha, hb, zero_pow (Fact.out : p.Prime).ne_zero, zero_mul, mul_zero, add_zero]
    · intro a b ha hb
      constructor
      · rw [map_add, map_add, ha.1, hb.1, add_zero]
      · rw [relativeFreeFiniteDeltaStep_map_add_of_left_zero N σ D q a b ha.1,
          ha.2, hb.2, add_zero]
  exact he.2

/-- 初期包含の核の二乗だけ異なる有限多項式のδ像は、通常射の下で一致する。 -/
theorem relativeFreeFiniteDeltaStep_map_eq_of_sub_mem_ker_square (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hfg : f - g ∈ (RingHom.ker (q.comp (relativeFreeFiniteStepInclusion N σ))) ^ 2) :
    q (relativeFreeFiniteDeltaStep N σ D f) =
      q (relativeFreeFiniteDeltaStep N σ D g) := by
  have hzero := relativeFreeFiniteDeltaStep_map_zero_of_mem_ker_square N σ D q hp (f - g) hfg
  have hinc : q (relativeFreeFiniteStepInclusion N σ (f - g)) = 0 := by
    exact (Ideal.pow_le_self (by decide : 2 ≠ 0)) hfg
  have he := relativeFreeFiniteDeltaStep_map_add_of_right_zero N σ D q g (f - g) hinc
  rw [add_sub_cancel, hzero, add_zero] at he
  exact he

/-- 二次誤差を含むp倍・d倍の正規形から、有限δ像の二つのp乗項を計算できる。 -/
theorem relativeFreeFiniteDeltaStep_map_of_normalForm (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (d : A) (hd : q (MvPolynomial.C d) = 0)
    (f r g h : MvPolynomial (σ × Fin (N + 1)) A)
    (hform : f - (r + (p : MvPolynomial (σ × Fin (N + 1)) A) * g + MvPolynomial.C d * h) ∈
      (RingHom.ker (q.comp (relativeFreeFiniteStepInclusion N σ))) ^ 2) :
    q (relativeFreeFiniteDeltaStep N σ D f) =
      q (relativeFreeFiniteDeltaStep N σ D r) +
        (q (relativeFreeFiniteStepInclusion N σ g)) ^ p +
          q (MvPolynomial.C (D.delta d)) *
            (q (relativeFreeFiniteStepInclusion N σ h)) ^ p := by
  rw [relativeFreeFiniteDeltaStep_map_eq_of_sub_mem_ker_square N σ D q hp _ _ hform]
  exact relativeFreeFiniteDeltaStep_map_perturbation N σ D q hp d hd r g h

end SerrePositivity.BhattScholze
