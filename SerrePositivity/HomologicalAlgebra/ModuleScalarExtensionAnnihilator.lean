module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Scalar extension preserves annihilation by the corresponding scalar -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
open scoped ChangeOfRings
variable {R B : Type u} [CommRing R] [CommRing B]

/-- The original extension of scalars carries a-annihilation to φ(a)-annihilation. -/
lemma scalarExtension_annihilated (φ : R →+* B) (a : R) (M : ModuleCat.{u} R)
    (h : ∀ x : M, a • x = 0) :
    ∀ x : (ModuleCat.extendScalars φ).obj M, φ a • x = 0 := by
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, hx, hy, zero_add]
  | tmul b m =>
    change (φ a * (show B from b)) ⊗ₜ[R,φ] m = 0
    have hh : (φ a * (show B from b)) ⊗ₜ[R,φ] m =
        b ⊗ₜ[R,φ] (a • m) := by
      exact TensorProduct.smul_tmul (R := R) (R' := R) a b m
    rw [hh, h, TensorProduct.tmul_zero]



end SerrePositivity
