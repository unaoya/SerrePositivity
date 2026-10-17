module
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # A scalar inverse for a map with annihilated kernel and cokernel -/
@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- Kernel and cokernel annihilators give a two-sided scalar inverse for the actual map.
Neither module is required to be finite, projective, free, or complete. -/
theorem exists_scalar_inverse_of_ker_coker_annihilated
    (f : M →ₗ[R] N) (a b : R)
    (hk : ∀ x : f.ker, a • x = 0)
    (hc : ∀ y : N ⧸ f.range, b • y = 0) :
    ∃ v : N →ₗ[R] M,
      v.comp f = (a * b) • LinearMap.id ∧ f.comp v = (a * b) • LinearMap.id := by
  have hker : f.ker ≤ LinearMap.ker (a • (LinearMap.id : M →ₗ[R] M)) := by
    intro x hx
    have hh := congrArg (fun z : f.ker => (z : M)) (hk ⟨x, hx⟩)
    exact hh
  let u : M ⧸ f.ker →ₗ[R] M := f.ker.liftQ (a • LinearMap.id) hker
  let v₀ : f.range →ₗ[R] M := u.comp f.quotKerEquivRange.symm.toLinearMap
  have hv₀ (x : M) : v₀ (f.rangeRestrict x) = a • x := by
    change u (f.quotKerEquivRange.symm ⟨f x, f.mem_range_self x⟩) = a • x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hfv (y : f.range) : f (v₀ y) = a • (y : N) := by
    obtain ⟨x, hx⟩ := y.property
    have he : f.rangeRestrict x = y := Subtype.ext hx
    rw [← he, hv₀, map_smul]
    rfl
  have hmem (y : N) : b • y ∈ f.range := by
    apply (Submodule.Quotient.mk_eq_zero f.range).mp
    change f.range.mkQ (b • y) = 0
    rw [map_smul]
    exact hc _
  let w : N →ₗ[R] f.range := (b • LinearMap.id).codRestrict f.range hmem
  let v : N →ₗ[R] M := v₀.comp w
  refine ⟨v, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change v₀ (b • f.rangeRestrict x) = (a * b) • x
    rw [map_smul, hv₀, smul_smul, mul_comm]
  · apply LinearMap.ext
    intro y
    change f (v₀ (w y)) = (a * b) • y
    rw [hfv]
    change a • (b • y) = (a * b) • y
    rw [smul_smul]

end SerrePositivity
