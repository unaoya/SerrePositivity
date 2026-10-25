module

public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPBaseChange
public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPFactorialEquiv
public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialFunctorial

/-! # 正則一元階乗部分環の実テンソル基底変更

具体的基底射による代数構造を明示する。通常の基底変更のみを扱う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
variable (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (y : A)
variable (hyA : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
variable (hyB : IsSMulRegular (B ⧸ Ideal.span {(p : B)})
  (Ideal.Quotient.mk (Ideal.span {(p : B)}) (algebraMap A B y)))
local notation "ysA" => fun _ : Unit ↦ y
local notation "ysB" => fun _ : Unit ↦ algebraMap A B y
local notation "SA" => pDivisionFactorialSubring p ysA
local notation "SB" => pDivisionFactorialSubring p ysB

/-- 正則一元階乗部分環の、指定された基底作用に関する実テンソル基底変更同型。 -/
def regularPrincipalDPBaseChangeEquiv :
    letI : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
    letI : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
    B ⊗[A] SA ≃ₐ[B] SB := by
  letI : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
  letI : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
  let eA : PrincipalDPPresentation A y ≃ₐ[A] SA :=
    { __ := principalDPFactorialEquiv hA hpA D y hyA
      commutes' := principalDPFactorialEquiv_coeff hA hpA D y hyA }
  let eB : PrincipalDPPresentation B (algebraMap A B y) ≃ₐ[B] SB :=
    { __ := principalDPFactorialEquiv hB hpB E (algebraMap A B y) hyB
      commutes' := principalDPFactorialEquiv_coeff hB hpB E (algebraMap A B y) hyB }
  exact ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) eA).symm.trans
    (principalDPBaseChangeEquiv hA hpA hB hpB y)).trans eB

/-- 実基底変更同型は指定したBの係数を保つ。 -/
theorem regularPrincipalDPBaseChangeEquiv_coeff (b : B) :
    letI : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
    letI : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
    regularPrincipalDPBaseChangeEquiv hA hpA hB hpB D E y hyA hyB (b ⊗ₜ[A] (1 : SA)) =
      pDivisionFactorialBase p ysB b := by
  let : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
  let : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
  exact (regularPrincipalDPBaseChangeEquiv hA hpA hB hpB D E y hyA hyB).commutes b

/-- 実基底変更同型の全階乗生成元の純テンソル上の具体式。 -/
theorem regularPrincipalDPBaseChangeEquiv_tmul_value (b : B) (n : ℕ) :
    letI : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
    letI : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
    regularPrincipalDPBaseChangeEquiv hA hpA hB hpB D E y hyA hyB
      (b ⊗ₜ[A] (⟨pDivisionFactorialValue p ysA () n,
        pDivisionFactorialSubring_value_mem ysA () n⟩ : SA)) =
      pDivisionFactorialBase p ysB b *
        (⟨pDivisionFactorialValue p ysB () n,
          pDivisionFactorialSubring_value_mem ysB () n⟩ : SB) := by
  let : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
  let : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
  dsimp only [regularPrincipalDPBaseChangeEquiv]
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_symm_apply,
    Algebra.TensorProduct.map_tmul]
  change principalDPFactorialEquiv hB hpB E (algebraMap A B y) hyB
    (principalDPBaseChangeEquiv hA hpA hB hpB y
      (b ⊗ₜ[A] (principalDPFactorialEquiv hA hpA D y hyA).symm
        ⟨pDivisionFactorialValue p ysA () n,
          pDivisionFactorialSubring_value_mem ysA () n⟩)) = _
  rw [← principalDPFactorialEquiv_generator hA hpA D y hyA n, RingEquiv.symm_apply_apply,
    principalDPBaseChangeEquiv_tmul_generator, map_mul,
    principalDPFactorialEquiv_coeff, principalDPFactorialEquiv_generator]


/-- 実基底変更同型の全純テンソル上の式は、既存の具体的部分環射で与えられる。 -/
theorem regularPrincipalDPBaseChangeEquiv_tmul (b : B) (a : SA) :
    letI : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
    letI : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
    regularPrincipalDPBaseChangeEquiv hA hpA hB hpB D E y hyA hyB (b ⊗ₜ[A] a) =
      pDivisionFactorialBase p ysB b * pDivisionFactorialMap hA (algebraMap A B) ysA a := by
  let : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
  let : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
  let e := regularPrincipalDPBaseChangeEquiv hA hpA hB hpB D E y hyA hyB
  have hmap : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := SA)).toRingHom =
      pDivisionFactorialMap hA (algebraMap A B) ysA := by
    apply pDivisionFactorialHom_ext ysA
    · intro r
      change e ((1 : B) ⊗ₜ[A] pDivisionFactorialBase p ysA r) = _
      have hr : (1 : B) ⊗ₜ[A] pDivisionFactorialBase p ysA r =
          algebraMap A B r ⊗ₜ[A] (1 : SA) := by
        change (1 : B) ⊗ₜ[A] algebraMap A SA r = algebraMap A B r ⊗ₜ[A] (1 : SA)
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        exact (TensorProduct.tmul_smul (R := A) r (1 : B) (1 : SA)).trans
          (TensorProduct.smul_tmul' r (1 : B) (1 : SA))
      rw [hr, regularPrincipalDPBaseChangeEquiv_coeff]
      exact (RingHom.congr_fun (pDivisionFactorialMap_comp_base hA (algebraMap A B) ysA) r).symm
    · intro s n
      cases s
      change e ((1 : B) ⊗ₜ[A] (⟨pDivisionFactorialValue p ysA () n,
        pDivisionFactorialSubring_value_mem ysA () n⟩ : SA)) = _
      rw [regularPrincipalDPBaseChangeEquiv_tmul_value, pDivisionFactorialMap_value,
        map_one, one_mul]
  have ht : b ⊗ₜ[A] a = (b ⊗ₜ[A] (1 : SA)) * ((1 : B) ⊗ₜ[A] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [ht, map_mul, regularPrincipalDPBaseChangeEquiv_coeff]
  exact congrArg (fun t : SB ↦ pDivisionFactorialBase p ysB b * t)
    (RingHom.congr_fun hmap a)

end SerrePositivity.BhattScholze
