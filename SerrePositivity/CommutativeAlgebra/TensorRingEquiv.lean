module
public import SerrePositivity.CommutativeAlgebra.PerfectCoefficientTensor

/-! # Ordinary tensor ring maps with compatible changes of the base ring -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct
variable {R R' A A' B B' : Type u}
    [CommRing R] [CommRing R'] [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']

/-- Map both factors while retaining a compatible map of the base ring. -/
def tensorMapOfCompatibleBase (φ : R →+* R') (f : A →+* A') (g : B →+* B')
    (hf : ∀ r, f (algebraMap R A r) = algebraMap R' A' (φ r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R' B' (φ r)) :
    A ⊗[R] B →+* A' ⊗[R'] B' := by
  let iA := (Algebra.TensorProduct.includeLeft : A' →ₐ[R'] A' ⊗[R'] B').toRingHom
  let iB := (Algebra.TensorProduct.includeRight : B' →ₐ[R'] A' ⊗[R'] B').toRingHom
  apply coefficientTensorLift (iA.comp f) (iB.comp g)
  intro r
  change iA (f (algebraMap R A r)) = iB (g (algebraMap R B r))
  rw [hf, hg]
  exact ((Algebra.TensorProduct.includeLeft : A' →ₐ[R'] A' ⊗[R'] B').commutes (φ r)).trans
    ((Algebra.TensorProduct.includeRight : B' →ₐ[R'] A' ⊗[R'] B').commutes (φ r)).symm

@[simp] lemma tensorMapOfCompatibleBase_tmul
    (φ : R →+* R') (f : A →+* A') (g : B →+* B')
    (hf : ∀ r, f (algebraMap R A r) = algebraMap R' A' (φ r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R' B' (φ r)) (a : A) (b : B) :
    tensorMapOfCompatibleBase φ f g hf hg (a ⊗ₜ[R] b) = f a ⊗ₜ[R'] g b := by
  change (f a ⊗ₜ[R'] (1 : B')) * ((1 : A') ⊗ₜ[R'] g b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Compatible presentations identify the original ordinary tensor rings. -/
def tensorRingEquivOfCompatibleBase (e : R ≃+* R') (f : A ≃+* A') (g : B ≃+* B')
    (hf : ∀ r, f (algebraMap R A r) = algebraMap R' A' (e r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R' B' (e r)) :
    A ⊗[R] B ≃+* A' ⊗[R'] B' := by
  have hf' : ∀ r, f.symm (algebraMap R' A' r) = algebraMap R A (e.symm r) := by
    intro r
    apply f.injective
    rw [f.apply_symm_apply, hf, e.apply_symm_apply]
  have hg' : ∀ r, g.symm (algebraMap R' B' r) = algebraMap R B (e.symm r) := by
    intro r
    apply g.injective
    rw [g.apply_symm_apply, hg, e.apply_symm_apply]
  let F := tensorMapOfCompatibleBase e.toRingHom f.toRingHom g.toRingHom hf hg
  let G := tensorMapOfCompatibleBase e.symm.toRingHom f.symm.toRingHom g.symm.toRingHom hf' hg'
  exact
    { F with
      invFun := G
      left_inv := fun x => by
        change G (F x) = x
        induction x using TensorProduct.inductionOn with
        | tmul a b => simp [F, G]
        | add x y hx hy => simp only [map_add, hx, hy]
      right_inv := fun x => by
        change F (G x) = x
        induction x using TensorProduct.inductionOn with
        | tmul a b => simp [F, G]
        | add x y hx hy => simp only [map_add, hx, hy] }

@[simp] lemma tensorRingEquivOfCompatibleBase_tmul
    (e : R ≃+* R') (f : A ≃+* A') (g : B ≃+* B')
    (hf : ∀ r, f (algebraMap R A r) = algebraMap R' A' (e r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R' B' (e r)) (a : A) (b : B) :
    tensorRingEquivOfCompatibleBase e f g hf hg (a ⊗ₜ[R] b) = f a ⊗ₜ[R'] g b :=
  tensorMapOfCompatibleBase_tmul e.toRingHom f.toRingHom g.toRingHom hf hg a b

end SerrePositivity
