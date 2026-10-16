import SerrePositivity.BhattScholze.CompatibleRootIdeal
import SerrePositivity.BhattScholze.CompatibleRootIdealFlat
import SerrePositivity.BhattScholze.CompatibleRootIdealTensor
import SerrePositivity.BhattScholze.CompatibleRootQuotientTor
import SerrePositivity.BhattScholze.CompatibleRootPerfectQuotient
import SerrePositivity.BhattScholze.CompatibleRootFamilyIdeal
import SerrePositivity.BhattScholze.PerfectCoefficientTensor
import Mathlib.Util.AssertNoSorry
import Lean

assert_no_sorry SerrePositivity.BhattScholze.compatibleRootIdeal
assert_no_sorry SerrePositivity.BhattScholze.span_root_zero_le_compatibleRootIdeal
assert_no_sorry SerrePositivity.BhattScholze.compatibleRoot_principal_monotone
assert_no_sorry SerrePositivity.BhattScholze.mem_compatibleRootIdeal_iff
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootIdeal_mul_self
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootIdeal_le_ker_of_root_zero
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootIdeal_map
assert_no_sorry SerrePositivity.BhattScholze.compatibleRoot_annihilator_le_succ
assert_no_sorry SerrePositivity.BhattScholze.compatibleRoot_transition_kills_kernel
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootIdeal_flat
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootIdealElement
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootIdeal_tensor_singleStage
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootIdealTensorMap
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootIdealTensorMap_injective
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootQuotient_tor_subsingleton
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootQuotient_derivedTensor_concentrated
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootIdeal_map_frobenius_eq
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootQuotient_perfectRing
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyIdeal
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal_le
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyIdeal_le_ker
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyIdeal_mul_self
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyIdeal_map_frobenius_eq
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyQuotient_perfectRing
assert_no_sorry SerrePositivity.BhattScholze.coefficientTensorLift
assert_no_sorry SerrePositivity.BhattScholze.coefficientTensorLift_tmul
assert_no_sorry SerrePositivity.BhattScholze.perfectCoefficientTensorRoot
assert_no_sorry SerrePositivity.BhattScholze.perfectCoefficientTensorRoot_tmul
assert_no_sorry SerrePositivity.BhattScholze.perfectCoefficientTensor_perfectRing

open Lean Elab Command
run_cmd do
  let names : List Name := [
    `SerrePositivity.BhattScholze.compatibleRootIdeal,
    `SerrePositivity.BhattScholze.span_root_zero_le_compatibleRootIdeal,
    `SerrePositivity.BhattScholze.compatibleRoot_principal_monotone,
    `SerrePositivity.BhattScholze.mem_compatibleRootIdeal_iff,
    `SerrePositivity.BhattScholze.compatibleRootIdeal_mul_self,
    `SerrePositivity.BhattScholze.compatibleRootIdeal_le_ker_of_root_zero,
    `SerrePositivity.BhattScholze.compatibleRootIdeal_map,
    `SerrePositivity.BhattScholze.compatibleRoot_annihilator_le_succ,
    `SerrePositivity.BhattScholze.compatibleRoot_transition_kills_kernel,
    `SerrePositivity.BhattScholze.compatibleRootIdeal_flat,
    `SerrePositivity.BhattScholze.compatibleRootIdealElement,
    `SerrePositivity.BhattScholze.compatibleRootIdeal_tensor_singleStage,
    `SerrePositivity.BhattScholze.compatibleRootIdealTensorMap,
    `SerrePositivity.BhattScholze.compatibleRootIdealTensorMap_injective,
    `SerrePositivity.BhattScholze.compatibleRootQuotient_tor_subsingleton,
    `SerrePositivity.BhattScholze.compatibleRootQuotient_derivedTensor_concentrated,
    `SerrePositivity.BhattScholze.compatibleRootIdeal_map_frobenius_eq,
    `SerrePositivity.BhattScholze.compatibleRootQuotient_perfectRing,
    `SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal,
    `SerrePositivity.BhattScholze.compatibleRootFamilyIdeal,
    `SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal_le,
    `SerrePositivity.BhattScholze.compatibleRootFamilyIdeal_le_ker,
    `SerrePositivity.BhattScholze.compatibleRootFamilyIdeal_mul_self,
    `SerrePositivity.BhattScholze.compatibleRootFamilyIdeal_map_frobenius_eq,
    `SerrePositivity.BhattScholze.compatibleRootFamilyQuotient_perfectRing,
    `SerrePositivity.BhattScholze.coefficientTensorLift,
    `SerrePositivity.BhattScholze.coefficientTensorLift_tmul,
    `SerrePositivity.BhattScholze.perfectCoefficientTensorRoot,
    `SerrePositivity.BhattScholze.perfectCoefficientTensorRoot_tmul,
    `SerrePositivity.BhattScholze.perfectCoefficientTensor_perfectRing]
  for n in names do
    unless (← getEnv).contains n do
      throwError "Existing BS constant was not retained: {n}"
  logInfo m!"All {names.length} existing BS constants are retained."

noncomputable section
universe u
open scoped TensorProduct
-- Original clients rewrite the old computational head with the old theorem name.
example {R A B D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] (f : A →+* D) (g : B →+* D)
    (h : ∀ r : R, f (algebraMap R A r) = g (algebraMap R B r)) (a : A) (b : B) :
    SerrePositivity.BhattScholze.coefficientTensorLift f g h (a ⊗ₜ[R] b) = f a * g b := by
  rw [SerrePositivity.BhattScholze.coefficientTensorLift_tmul]

example {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    SerrePositivity.BhattScholze.compatibleRootIdeal ρ *
      SerrePositivity.BhattScholze.compatibleRootIdeal ρ =
        SerrePositivity.BhattScholze.compatibleRootIdeal ρ := by
  rw [SerrePositivity.BhattScholze.compatibleRootIdeal_mul_self ρ hρ]
