module

public import SerrePositivity.CommutativeAlgebra.PerfectCoefficientTensor
/-! # Tensor automorphisms with a specified coefficient automorphism

The factor maps commute with the same base map, rather than being R-linear.
Their inverses commute with the inverse base map. No flatness is required.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open scoped TensorProduct
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Factor endomorphisms over the same base endomorphism induce a ring endomorphism. -/
def coefficientTensorEndomorphism (fR : R →+* R) (fS : S →+* S) (fT : T →+* T)
    (hS : ∀ r, fS (algebraMap R S r) = algebraMap R S (fR r))
    (hT : ∀ r, fT (algebraMap R T r) = algebraMap R T (fR r)) : S ⊗[R] T →+* S ⊗[R] T := by
  let l := (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom
  let r := (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
  apply coefficientTensorLift (l.comp fS) (r.comp fT)
  intro x
  change l (fS (algebraMap R S x)) = r (fT (algebraMap R T x))
  rw [hS, hT]
  exact (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes (fR x) |>.trans
    ((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).commutes (fR x)).symm

/-- The induced tensor map acts factorwise on pure tensors. -/
lemma coefficientTensorEndomorphism_tmul (fR : R →+* R) (fS : S →+* S) (fT : T →+* T)
    (hS : ∀ r, fS (algebraMap R S r) = algebraMap R S (fR r))
    (hT : ∀ r, fT (algebraMap R T r) = algebraMap R T (fR r)) (s : S) (t : T) :
    coefficientTensorEndomorphism fR fS fT hS hT (s ⊗ₜ[R] t) = fS s ⊗ₜ[R] fT t := by
  rw [coefficientTensorEndomorphism, coefficientTensorLift_tmul]
  change (fS s ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] fT t) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The inverse factor automorphism commutes with the inverse coefficient automorphism. -/
lemma coefficientTensorAutomorphism_inverse_compat (eR : R ≃+* R) (eS : S ≃+* S)
    (hS : ∀ r, eS (algebraMap R S r) = algebraMap R S (eR r)) (r : R) :
    eS.symm (algebraMap R S r) = algebraMap R S (eR.symm r) := by
  apply eS.injective
  rw [eS.apply_symm_apply, hS, eR.apply_symm_apply]

/-- Compatible automorphisms induce a ring automorphism of the original tensor. -/
def coefficientTensorAutomorphism (eR : R ≃+* R) (eS : S ≃+* S) (eT : T ≃+* T)
    (hS : ∀ r, eS (algebraMap R S r) = algebraMap R S (eR r))
    (hT : ∀ r, eT (algebraMap R T r) = algebraMap R T (eR r)) : S ⊗[R] T ≃+* S ⊗[R] T := by
  let f := coefficientTensorEndomorphism eR.toRingHom eS.toRingHom eT.toRingHom hS hT
  let g := coefficientTensorEndomorphism eR.symm.toRingHom eS.symm.toRingHom eT.symm.toRingHom
    (coefficientTensorAutomorphism_inverse_compat eR eS hS)
    (coefficientTensorAutomorphism_inverse_compat eR eT hT)
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · change Function.LeftInverse g f
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s t =>
      dsimp only [f, g]
      rw [coefficientTensorEndomorphism_tmul, coefficientTensorEndomorphism_tmul]
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  · change Function.RightInverse g f
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s t =>
      dsimp only [f, g]
      rw [coefficientTensorEndomorphism_tmul, coefficientTensorEndomorphism_tmul]
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply]
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The forward tensor automorphism acts factorwise. -/
lemma coefficientTensorAutomorphism_tmul (eR : R ≃+* R) (eS : S ≃+* S) (eT : T ≃+* T)
    (hS : ∀ r, eS (algebraMap R S r) = algebraMap R S (eR r))
    (hT : ∀ r, eT (algebraMap R T r) = algebraMap R T (eR r)) (s : S) (t : T) :
    coefficientTensorAutomorphism eR eS eT hS hT (s ⊗ₜ[R] t) = eS s ⊗ₜ[R] eT t :=
  coefficientTensorEndomorphism_tmul eR.toRingHom eS.toRingHom eT.toRingHom hS hT s t
/-- The inverse tensor automorphism acts by the inverse factor maps. -/
lemma coefficientTensorAutomorphism_symm_tmul (eR : R ≃+* R) (eS : S ≃+* S) (eT : T ≃+* T)
    (hS : ∀ r, eS (algebraMap R S r) = algebraMap R S (eR r))
    (hT : ∀ r, eT (algebraMap R T r) = algebraMap R T (eR r)) (s : S) (t : T) :
    (coefficientTensorAutomorphism eR eS eT hS hT).symm (s ⊗ₜ[R] t) =
      eS.symm s ⊗ₜ[R] eT.symm t :=
  coefficientTensorEndomorphism_tmul eR.symm.toRingHom eS.symm.toRingHom eT.symm.toRingHom
    (coefficientTensorAutomorphism_inverse_compat eR eS hS)
    (coefficientTensorAutomorphism_inverse_compat eR eT hT) s t

end SerrePositivity
