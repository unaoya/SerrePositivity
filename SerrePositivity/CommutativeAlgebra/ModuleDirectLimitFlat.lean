module

public import SerrePositivity.CommutativeAlgebra.DirectLimitFlat
public import Mathlib.Algebra.Colimit.Module

/-! # Flatness of the standard module direct limit

The existing theorem for the disjoint-union model is transported through Mathlib's
canonical comparison. Transition maps need not be injective.
-/

@[expose] public section
namespace SerrePositivity

variable {R ι : Type*} [CommRing R] [Preorder ι] [DecidableEq ι]
variable [IsDirectedOrder ι] [Nonempty ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (f : ∀ i j, i ≤ j → M i →ₗ[R] M j) [DirectedSystem M (f · · ·)]

/-- A directed limit of flat modules is flat, in the standard `Module.DirectLimit` model. -/
theorem moduleDirectLimit_flat [∀ i, Module.Flat R (M i)] :
    Module.Flat R (Module.DirectLimit M f) := by
  have := directLimit_flat M f
  exact Module.Flat.of_linearEquiv (Module.DirectLimit.linearEquiv M f)

end SerrePositivity
