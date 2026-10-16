module

public import Mathlib.RingTheory.Flat.Basic

/-! # Scalar annihilator bounds pass to flat modules

This supplies a uniform torsion bound for the projective terms used in G9.
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A scalar killing the kernel of multiplication by `a` on the ring also kills
the corresponding kernel on every flat module. -/
theorem smul_eq_zero_of_flat_of_mul_kernel [Module.Flat R M] (a b : R)
    (h : ∀ r : R, a * r = 0 → b * r = 0) (x : M) (hx : a • x = 0) :
    b • x = 0 := by
  let f : R →ₗ[R] R := a • LinearMap.id
  let K := f.ker
  have he : Function.Exact K.subtype f := f.exact_subtype_ker_map
  have ht := Module.Flat.rTensor_exact (M := M) he
  have hz : f.rTensor M ((1 : R) ⊗ₜ[R] x) = 0 := by
    simpa [f, TensorProduct.smul_tmul'] using congrArg (fun y : M ↦ (1 : R) ⊗ₜ[R] y) hx
  obtain ⟨z, hz⟩ := (ht ((1 : R) ⊗ₜ[R] x)).mp hz
  have hk : ∀ z : K ⊗[R] M, b • (TensorProduct.lid R M) (K.subtype.rTensor M z) = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r y =>
      have hrf : f (r : R) = 0 := r.property
      have hr : b * (r : R) = 0 := h r hrf
      simp [smul_smul, hr]
    | add z w hz hw => simp only [map_add, smul_add, hz, hw, add_zero]
  simpa only [hz, TensorProduct.lid_tmul, one_smul] using hk z

/-- Flat modules inherit the same bound on power torsion as the coefficient ring. -/
theorem flat_power_torsion_bound [Module.Flat R M] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) :
    ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0 :=
  fun n x hx ↦ smul_eq_zero_of_flat_of_mul_kernel (a ^ n) (a ^ N) (h n) x hx

/-- A scalar sending a ring kernel into a principal ideal sends the kernel on
a flat module into the corresponding scalar image. -/
theorem smul_eq_smul_of_flat_of_mul_kernel [Module.Flat R M] (a b c : R)
    (h : ∀ r : R, a * r = 0 → ∃ s : R, b * r = c * s)
    (x : M) (hx : a • x = 0) : ∃ y : M, b • x = c • y := by
  let f : R →ₗ[R] R := a • LinearMap.id
  let K := f.ker
  have he : Function.Exact K.subtype f := f.exact_subtype_ker_map
  have ht := Module.Flat.rTensor_exact (M := M) he
  have hz : f.rTensor M ((1 : R) ⊗ₜ[R] x) = 0 := by
    simpa [f, TensorProduct.smul_tmul'] using congrArg (fun y : M ↦ (1 : R) ⊗ₜ[R] y) hx
  obtain ⟨z, hz⟩ := (ht ((1 : R) ⊗ₜ[R] x)).mp hz
  have hk : ∀ z : K ⊗[R] M,
      ∃ y : M, b • (TensorProduct.lid R M) (K.subtype.rTensor M z) = c • y := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r y =>
      obtain ⟨s, hs⟩ := h r (show f (r : R) = 0 from r.property)
      refine ⟨s • y, ?_⟩
      simpa [smul_smul] using congrArg (fun q : R ↦ q • y) hs
    | add z w hz hw =>
      obtain ⟨y, hy⟩ := hz
      obtain ⟨v, hv⟩ := hw
      exact ⟨y + v, by simp only [map_add, smul_add, hy, hv]⟩
  simpa only [hz, TensorProduct.lid_tmul, one_smul] using hk z

end SerrePositivity
