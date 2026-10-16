module
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Scalar factorizations through a finite free comparison module -/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- A scalar killing the cokernel lifts its action on the finite free target. -/
lemma exists_finiteFree_scalar_lift (r : ℕ) (f : M →ₗ[R] (Fin r → R)) (a : R)
    (ha : ∀ y : (Fin r → R) ⧸ f.range, a • y = 0) :
    ∃ v : (Fin r → R) →ₗ[R] M, f.comp v = a • LinearMap.id := by
  classical
  let b := Pi.basisFun R (Fin r)
  have hmem (j : Fin r) : a • b j ∈ f.range := by
    apply (Submodule.Quotient.mk_eq_zero f.range).mp
    change f.range.mkQ (a • b j) = 0
    rw [map_smul]
    exact ha _
  choose z hz using fun j : Fin r => hmem j
  let v := b.constr R z
  refine ⟨v, ?_⟩
  apply b.ext
  intro j
  change f (v (b j)) = a • b j
  rw [show v (b j) = z j from b.constr_basis R _ j]
  exact hz j

/-- The product of kernel and cokernel annihilators factors through the same finite free module.
The source need not be finite, reduced, or torsion free. -/
lemma exists_scalar_factorization_through_finiteFree
    (r : ℕ) (f : M →ₗ[R] (Fin r → R)) (a b : R)
    (ha : ∀ y : (Fin r → R) ⧸ f.range, a • y = 0)
    (hb : ∀ x : f.ker, b • x = 0) :
    ∃ v : (Fin r → R) →ₗ[R] M, v.comp f = (a * b) • LinearMap.id := by
  obtain ⟨v, hv⟩ := exists_finiteFree_scalar_lift r f a ha
  refine ⟨b • v, ?_⟩
  apply LinearMap.ext
  intro x
  have hker : v (f x) - a • x ∈ f.ker := by
    change f (v (f x) - a • x) = 0
    rw [map_sub, map_smul]
    have h := LinearMap.congr_fun hv (f x)
    change f (v (f x)) = a • f x at h
    rw [h, sub_self]
  have h := congrArg (fun z : f.ker => (z : M)) (hb ⟨v (f x) - a • x, hker⟩)
  change b • (v (f x) - a • x) = 0 at h
  rw [smul_sub, sub_eq_zero] at h
  change b • v (f x) = (a * b) • x
  simpa only [smul_smul, mul_comm] using h

end SerrePositivity
