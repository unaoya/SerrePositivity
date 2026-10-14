module

public import SerrePositivity.KTheory.Adams.TensorSquareEvaluation

/-! # The cyclic Adams operation of degree two -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace Adams
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

/-- The cyclic Adams operation on the closed-support Grothendieck group. -/
def cyclicTwo : K0WithSupport Z →+ K0WithSupport Z :=
  K0WithSupport.lift Z (tensorSquareEvaluation Z)
    (tensorSquareEvaluation_iso Z) (tensorSquareEvaluation_triangle Z)

@[simp]
lemma cyclicTwo_mk (X : SupportedPerfectHomotopyOn Z) :
    cyclicTwo Z (K0WithSupport.mk Z X) = tensorSquareEvaluation Z X :=
  K0WithSupport.lift_mk Z (tensorSquareEvaluation Z)
    (tensorSquareEvaluation_iso Z) (tensorSquareEvaluation_triangle Z) X

lemma cyclicTwo_mk_concrete (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    cyclicTwo Z (K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) =
      tensorSquareClass P Z hp hs := cyclicTwo_mk Z _

lemma cyclicTwo_unique (F : K0WithSupport Z →+ K0WithSupport Z)
    (h : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P),
      F (K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) = tensorSquareClass P Z hp hs) :
    F = cyclicTwo Z := by
  apply K0WithSupport.hom_ext
  intro X
  rw [cyclicTwo_mk]
  exact h (supportedPerfectRepresentative X) (supportedPerfectRepresentative_perfect X)
    (supportedPerfectRepresentative_support X)

end Adams
end SerrePositivity
