module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Flat.Basic

/-! # Bounded power torsion in finite coefficients and their flat tensors

The bound belongs to the test module, not to the coefficient ring. This is the
bound needed when tensoring a resolution of the unresolved perfectoid algebra
with a finite module that may have p-torsion.
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct
variable {R M F : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F]

/-- Ascending scalar kernels stabilize on every Noetherian module. -/
lemma exists_power_torsion_bound_of_noetherian [IsNoetherian R M] (a : R) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0 := by
  let K : ℕ →o Submodule R M :=
    { toFun := fun n => (a ^ n • (LinearMap.id : M →ₗ[R] M)).ker
      monotone' := by
        intro m n h x hx
        change a ^ m • x = 0 at hx
        change a ^ n • x = 0
        rw [show a ^ n = a ^ (n - m) * a ^ m by
          rw [← pow_add, Nat.sub_add_cancel h], mul_smul, hx, smul_zero] }
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  refine ⟨N, fun n x hx => ?_⟩
  have hx' : x ∈ K (N + n) := K.monotone (Nat.le_add_left n N) hx
  rw [← hN (N + n) (Nat.le_add_right N n)] at hx'
  exact hx'

/-- Finite modules over Noetherian rings have their own uniform power-torsion
bound; the scalar need not be regular. -/
lemma exists_power_torsion_bound_of_finite [IsNoetherianRing R] [Module.Finite R M]
    (a : R) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0 :=
  exists_power_torsion_bound_of_noetherian a

/-- Tensoring with a flat module preserves a scalar bound on a kernel in M. -/
lemma smul_eq_zero_tensor_of_flat_of_smul_kernel [Module.Flat R F] (a b : R)
    (h : ∀ x : M, a • x = 0 → b • x = 0)
    (x : M ⊗[R] F) (hx : a • x = 0) : b • x = 0 := by
  let f : M →ₗ[R] M := a • LinearMap.id
  let K := f.ker
  have he : Function.Exact K.subtype f := f.exact_subtype_ker_map
  have ht := Module.Flat.rTensor_exact (M := F) he
  have hz : f.rTensor F x = 0 := by
    simpa [f] using hx
  obtain ⟨z, hz⟩ := (ht x).mp hz
  have hk : ∀ z : K ⊗[R] F, b • K.subtype.rTensor F z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul y v =>
      have hy : b • (y : M) = 0 := h y y.property
      simp [TensorProduct.smul_tmul', hy]
    | add z w hz hw => simp only [map_add, smul_add, hz, hw, add_zero]
  simpa only [hz] using hk z

/-- The same uniform bound passes from a test module to all its flat tensors. -/
lemma flat_tensor_power_torsion_bound [Module.Flat R F] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0) :
    ∀ n : ℕ, ∀ x : M ⊗[R] F, a ^ n • x = 0 → a ^ N • x = 0 :=
  fun n x hx => smul_eq_zero_tensor_of_flat_of_smul_kernel (a ^ n) (a ^ N) (h n) x hx

end SerrePositivity
