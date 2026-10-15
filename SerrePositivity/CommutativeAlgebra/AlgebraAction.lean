module
public import Mathlib.Algebra.Algebra.Hom

/-! # Parameter and composition formulas for algebra actions -/
@[expose] public section
namespace SerrePositivity
variable {A T : Type*} [CommSemiring A] [Semiring T] [Algebra A T]

/-- An algebra endomorphism fixes every family of parameters from the base. -/
lemma algebraHom_parameters {ι : Type*} (f : T →ₐ[A] T) (z : ι → A) :
    f.toRingHom ∘ (algebraMap A T ∘ z) = algebraMap A T ∘ z := by
  funext j
  exact f.commutes (z j)

variable {G : Type*} [Monoid G] [MulSemiringAction G T] [SMulCommClass G A T]

/-- The unit acts by the identity ring homomorphism. -/
lemma algebraActionRingHom_one :
    (MulSemiringAction.toAlgHom A T (1 : G)).toRingHom = RingHom.id T := by
  ext x
  exact one_smul G x

/-- Multiplication acts by composition in the order used by scalar extension. -/
lemma algebraActionRingHom_mul (g h : G) :
    (MulSemiringAction.toAlgHom A T (g * h)).toRingHom =
      (MulSemiringAction.toAlgHom A T g).toRingHom.comp
        (MulSemiringAction.toAlgHom A T h).toRingHom := by
  ext x
  exact mul_smul g h x

end SerrePositivity
