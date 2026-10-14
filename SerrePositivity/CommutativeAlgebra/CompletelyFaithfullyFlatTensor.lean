module
public import SerrePositivity.CommutativeAlgebra.CompletelyFaithfullyFlatPowers

/-! # Completely faithful flatness detects ordinary tensor maps on power-torsion modules -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- Ordinary tensoring reflects zero maps between finite-power-torsion modules. -/
theorem power_torsion_rTensor_eq_zero_iff
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (hN : ∀ x : N, a ^ n • x = 0) (hN' : ∀ x : N', a ^ n • x = 0)
    (f : N →ₗ[R] N') : f.rTensor M = 0 ↔ f = 0 := by
  constructor
  · intro hf
    let A := R ⧸ Ideal.span {a ^ n}
    let _ := principalPowerTorsionModule a n N hN
    let _ := principalPowerTorsionModule a n N' hN'
    let fA := principalPowerTorsionLinearMap a n hN hN' f
    have : Module.FaithfullyFlat A (A ⊗[R] M) :=
      faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat a M hM n
    have hq : fA.rTensor (A ⊗[R] M) = 0 := by
      apply TensorProduct.ext'
      intro x y
      induction y using TensorProduct.inductionOn with
      | tmul r m =>
        apply (AlgebraTensorModule.cancelBaseChange R A A N' M).injective
        simp only [LinearMap.rTensor_tmul, LinearMap.zero_apply,
          map_zero]
        change (r • fA x) ⊗ₜ[R] m = 0
        have hz : fA (r • x) ⊗ₜ[R] m = 0 :=
          congrArg (fun g => g ((r • x) ⊗ₜ[R] m)) hf
        simpa only [fA.map_smul] using hz
      | add y z hy hz =>
        simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hy hz
    have hz := (Module.FaithfullyFlat.zero_iff_rTensor_zero A (A ⊗[R] M) fA).mpr hq
    exact (principalPowerTorsionLinearMap_eq_zero_iff a n hN hN' f).mp hz
  · rintro rfl
    simp

/-- The same reflection in the left tensor convention used by scalar extension. -/
theorem power_torsion_ordinary_lTensor_eq_zero_iff
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (hN : ∀ x : N, a ^ n • x = 0) (hN' : ∀ x : N', a ^ n • x = 0)
    (f : N →ₗ[R] N') : f.lTensor M = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply (power_torsion_rTensor_eq_zero_iff a M hM n hN hN' f).mp
    ext x m
    have hz := congrArg (fun g => (TensorProduct.comm R M N') (g (m ⊗ₜ[R] x))) hf
    simpa using hz
  · rintro rfl
    simp

end SerrePositivity
