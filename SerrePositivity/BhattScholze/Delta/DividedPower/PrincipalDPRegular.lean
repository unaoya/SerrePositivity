module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPPrimeBasis
public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPPresentation
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient
public import Mathlib.Tactic.Ring

/-! # 正則一元入力での実分冪表示環のp正則性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
local notation "B₀" => DividedPowerAlgebra A A

/-- 一元分冪代数の一次生成元のp乗はpで割れる。 -/
theorem rankOneDPGenerator_pow_mem_prime :
    (DividedPowerAlgebra.dp A 1 (1 : A)) ^ p ∈ Ideal.span {(p : B₀)} := by
  rw [← DividedPowerAlgebra.natFactorial_mul_dp_eq]
  apply Ideal.mul_mem_right
  apply Ideal.mem_span_singleton.mpr
  exact map_dvd (Nat.castRingHom B₀)
    (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)

/-- p乗算が単射でy mod pが正則なら、表示関係もmod pで正則。p局所性は不要。 -/
theorem principalDPRelation_mod_p_isSMulRegular_of_p_mul_injective
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    IsSMulRegular (B₀ ⧸ Ideal.span {(p : B₀)})
      (Ideal.Quotient.mk (Ideal.span {(p : B₀)})
        (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A B₀ y)) := by
  let : Module.Free A B₀ := rankOneDPAny_moduleFree A
  let q := Ideal.Quotient.mk (Ideal.span {(p : B₀)})
  let x := q (DividedPowerAlgebra.dp A 1 (1 : A))
  let c := q (algebraMap A B₀ y)
  have hc : IsSMulRegular (B₀ ⧸ Ideal.span {(p : B₀)}) c := by
    have h := SerrePositivity.isSMulRegular_mod_of_flat (S := B₀) (p : A) y hpA hy
    have aux (a : B₀) (he : a = (p : B₀))
        (ha : IsSMulRegular (B₀ ⧸ Ideal.span {a})
          (Ideal.Quotient.mk (Ideal.span {a}) (algebraMap A B₀ y))) :
        IsSMulRegular (B₀ ⧸ Ideal.span {(p : B₀)}) c := by
      subst a
      exact ha
    exact aux _ (map_natCast (algebraMap A B₀) p) h
  have hx : x ^ p = 0 := by
    change q (DividedPowerAlgebra.dp A 1 (1 : A)) ^ p = 0
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr rankOneDPGenerator_pow_mem_prime
  change Function.Injective (fun z : B₀ ⧸ Ideal.span {(p : B₀)} ↦ q
    (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A B₀ y) * z)
  simp only [map_sub]
  change Function.Injective (fun z : B₀ ⧸ Ideal.span {(p : B₀)} ↦ (x - c) * z)
  intro z t hzt
  apply sub_eq_zero.mp
  have hxc : x * (z - t) = c * (z - t) := by
    apply sub_eq_zero.mp
    rw [← sub_mul, mul_sub]
    exact sub_eq_zero.mpr hzt
  have hn : ∀ n : ℕ, x ^ n * (z - t) = c ^ n * (z - t) := by
    intro n
    induction n with
    | zero => simp only [pow_zero, one_mul]
    | succ n ih =>
        calc
          _ = x ^ n * (x * (z - t)) := by ring
          _ = x ^ n * (c * (z - t)) := by rw [hxc]
          _ = c * (x ^ n * (z - t)) := by ring
          _ = c * (c ^ n * (z - t)) := by rw [ih]
          _ = _ := by ring
  apply hc.pow p
  change c ^ p * (z - t) = c ^ p * 0
  rw [mul_zero, ← hn p, hx, zero_mul]

set_option linter.unusedVariables false in
/-- y mod pが正則なら、表示関係γ₁(1)−yも一元分冪代数のmod pで正則。 -/
theorem principalDPRelation_mod_p_isSMulRegular
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    IsSMulRegular (B₀ ⧸ Ideal.span {(p : B₀)})
      (Ideal.Quotient.mk (Ideal.span {(p : B₀)})
        (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A B₀ y)) :=
  principalDPRelation_mod_p_isSMulRegular_of_p_mul_injective hpA y hy

/-- p乗算が単射でy mod pが正則なら、具体的分冪表示環もp正則。p局所性は不要。 -/
theorem principalDPPresentation_p_mul_injective_of_regular_mod
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    Function.Injective (fun b : PrincipalDPPresentation A y ↦
      (p : PrincipalDPPresentation A y) * b) := by
  have hp : IsSMulRegular B₀ (p : B₀) := by
    simpa only [map_natCast] using rankOneDPAny_isSMulRegular (p : A) hpA
  have h := SerrePositivity.isSMulRegular_quotient_span_of_regular_mod B₀ (p : B₀)
    (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A B₀ y)
    hp
    (principalDPRelation_mod_p_isSMulRegular_of_p_mul_injective hpA y hy)
  simpa only [IsSMulRegular, smul_eq_mul, map_natCast, PrincipalDPPresentation,
    principalDPRelationIdeal] using h

set_option linter.unusedVariables false in
/-- 正則一元入力の下で、具体的分冪表示環にはpねじれがない。 -/
theorem principalDPPresentation_p_mul_injective
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    Function.Injective (fun b : PrincipalDPPresentation A y ↦
      (p : PrincipalDPPresentation A y) * b) :=
  principalDPPresentation_p_mul_injective_of_regular_mod hpA y hy

end SerrePositivity.BhattScholze
