module

public import SerrePositivity.CommutativeAlgebra.ScalarIsogenyInverse
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # スカラー逆を元の通常 tensor の単位写像へ移す

既存の核・余核からのスカラー逆を tensor に適用する。
加群の平坦性・有限性は不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R T M : Type u) [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [Module R M]

/-- 元の R→T の核・余核の零化から、元の M→T⊗R M の両側スカラー逆を作る。 -/
theorem exists_tensor_unit_scalar_inverse_of_ker_coker_annihilated
    (a b : R)
    (hk : ∀ x : (Algebra.linearMap R T).ker, a • x = 0)
    (hc : ∀ y : T ⧸ (Algebra.linearMap R T).range, b • y = 0) :
    let u := TensorProduct.mk R T M (1 : T)
    ∃ w : T ⊗[R] M →ₗ[R] M,
      w.comp u = (a * b) • LinearMap.id ∧ u.comp w = (a * b) • LinearMap.id := by
  let u := TensorProduct.mk R T M (1 : T)
  obtain ⟨v, hv, hf⟩ := exists_scalar_inverse_of_ker_coker_annihilated
    (Algebra.linearMap R T) a b hk hc
  let w : T ⊗[R] M →ₗ[R] M :=
    (TensorProduct.lid R M).toLinearMap.comp (LinearMap.rTensor M v)
  have hw (t : T) (m : M) : w (t ⊗ₜ[R] m) = v t • m := by
    change (TensorProduct.lid R M) (LinearMap.rTensor M v (t ⊗ₜ[R] m)) = v t • m
    rw [LinearMap.rTensor_tmul]
    exact TensorProduct.lid_tmul m (v t)
  have hv1 : v (1 : T) = a * b := by
    have h := LinearMap.congr_fun hv 1
    change v (algebraMap R T 1) = (a * b) • (1 : R) at h
    simpa only [map_one, smul_eq_mul, mul_one] using h
  refine ⟨w, ?_, ?_⟩
  · ext m
    change w ((1 : T) ⊗ₜ[R] m) = (a * b) • m
    rw [hw, hv1]
  · apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t m =>
        change (1 : T) ⊗ₜ[R] w (t ⊗ₜ[R] m) = (a * b) • (t ⊗ₜ[R] m)
        rw [hw]
        have hft : algebraMap R T (v t) = (a * b) • t := LinearMap.congr_fun hf t
        calc
          (1 : T) ⊗ₜ[R] (v t • m) = ((v t : R) • (1 : T)) ⊗ₜ[R] m :=
            (TensorProduct.smul_tmul _ _ _).symm
          _ = algebraMap R T (v t) ⊗ₜ[R] m := by rw [Algebra.smul_def, mul_one]
          _ = ((a * b) • t) ⊗ₜ[R] m := by rw [hft]
          _ = (a * b) • (t ⊗ₜ[R] m) := (TensorProduct.smul_tmul' _ _ _).symm
    | add x y hx hy =>
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
          map_add, smul_add, hx, hy]

/-- 同じスカラー積が、元の通常 tensor の単位の核・余核をともに消す。 -/
theorem tensor_unit_ker_coker_annihilated
    (a b : R)
    (hk : ∀ x : (Algebra.linearMap R T).ker, a • x = 0)
    (hc : ∀ y : T ⧸ (Algebra.linearMap R T).range, b • y = 0) :
    let u := TensorProduct.mk R T M (1 : T)
    (∀ x : u.ker, (a * b) • x = 0) ∧
      (∀ y : (T ⊗[R] M) ⧸ u.range, (a * b) • y = 0) := by
  let u := TensorProduct.mk R T M (1 : T)
  obtain ⟨w, hw, hu⟩ :=
    exists_tensor_unit_scalar_inverse_of_ker_coker_annihilated R T M a b hk hc
  constructor
  · intro x
    apply Subtype.ext
    have h := LinearMap.congr_fun hw (x : M)
    change w (u (x : M)) = (a * b) • (x : M) at h
    rw [x.property, map_zero] at h
    exact h.symm
  · intro y
    obtain ⟨y, rfl⟩ := u.range.mkQ_surjective y
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero u.range).mpr
    exact ⟨w y, LinearMap.congr_fun hu y⟩

end SerrePositivity
