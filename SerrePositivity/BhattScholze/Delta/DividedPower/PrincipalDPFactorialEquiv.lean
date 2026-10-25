module

public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPRegular
public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPFactorialKernel

/-! # 正則一元分冪表示環と具体的階乗部分環の実同型 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))

include hpA hy

/-- 正則一元入力では、表示環から階乗部分環への実比較射は単射。 -/
theorem principalDPToFactorial_injective : Function.Injective (principalDPToFactorial hA D y) := by
  intro b c hbc
  apply sub_eq_zero.mp
  have hz : principalDPToFactorial hA D y (b - c) = 0 := by
    rw [map_sub, hbc, sub_self]
  obtain ⟨n, hn⟩ := (principalDPToFactorial_eq_zero_iff hA D y (b - c)).mp hz
  have hr : IsLeftRegular (p : PrincipalDPPresentation A y) :=
    principalDPPresentation_p_mul_injective hA hpA y hy
  apply hr.pow n
  change (p : PrincipalDPPresentation A y) ^ n * (b - c) =
    (p : PrincipalDPPresentation A y) ^ n * 0
  rw [mul_zero]
  exact hn

/-- 正則一元表示環と具体的階乗部分環の、実比較射による環同型。 -/
def principalDPFactorialEquiv :
    PrincipalDPPresentation A y ≃+* pDivisionFactorialSubring p (fun _ : Unit ↦ y) :=
  RingEquiv.ofBijective (principalDPToFactorial hA D y)
    ⟨principalDPToFactorial_injective hA hpA D y hy, principalDPToFactorial_surjective hA D y⟩

/-- 実比較同型は元の係数環の射を保つ。 -/
theorem principalDPFactorialEquiv_coeff (a : A) :
    principalDPFactorialEquiv hA hpA D y hy (algebraMap A (PrincipalDPPresentation A y) a) =
      pDivisionFactorialBase p (fun _ : Unit ↦ y) a :=
  principalDPToFactorial_coeff hA D y a

/-- 実比較同型は全標準分冪生成元を指定された階乗分母へ送る。 -/
theorem principalDPFactorialEquiv_generator (n : ℕ) :
    principalDPFactorialEquiv hA hpA D y hy (principalDPGenerator y n) =
      ⟨pDivisionFactorialValue p (fun _ : Unit ↦ y) () n,
        pDivisionFactorialSubring_value_mem (fun _ : Unit ↦ y) () n⟩ :=
  principalDPToFactorial_generator hA D y n

end SerrePositivity.BhattScholze
