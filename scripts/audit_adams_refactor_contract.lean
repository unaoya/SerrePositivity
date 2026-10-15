import SerrePositivity.Inputs.IntersectionTheory
import Mathlib.Util.AssertNoSorry

open CategoryTheory TensorProduct SerrePositivity
universe u

-- Keep the public statement, including universes and all assumptions, explicit.
example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    chi R M N = 0 :=
  Inputs.intersectionVanishing R M N hfin hdim

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ F : CochainComplex (ModuleCat.{u} R) ℤ,
      Nonempty (IsResolutionOf F (ModuleCat.of R M)) ∧
      (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → CategoryTheory.Limits.IsZero (F.X i)) ∧
      (∀ i, Module.Free R (F.X i)) ∧ (∀ i, Module.Finite R (F.X i)) :=
  Inputs.regularResolution R M

assert_no_sorry SerrePositivity.Inputs.intersectionVanishing
assert_no_sorry SerrePositivity.Inputs.regularResolution
#print axioms SerrePositivity.Inputs.intersectionVanishing
