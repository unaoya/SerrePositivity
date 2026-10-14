module

public import SerrePositivity.KTheory.Adams.TensorCubeEvaluation
public import SerrePositivity.KTheory.CoefficientLinearExtension

/-! # The cyclic Adams operation of degree three with extended coefficients -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams
variable (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0)
variable (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

/-- Descend the cubic evaluation to the integer Grothendieck group first. -/
def cyclicThreeValue : K0WithSupport Z →+ K0WithSupport.Coefficients E Z :=
  K0WithSupport.lift Z (tensorCubeEvaluation E t ht ζ Z)
    (tensorCubeEvaluation_iso E t ht ζ Z) (tensorCubeEvaluation_triangle E t ht ζ Z hζ)

@[simp]
lemma cyclicThreeValue_mk (X : SupportedPerfectHomotopyOn Z) :
    cyclicThreeValue E t ht ζ hζ Z (K0WithSupport.mk Z X) = tensorCubeEvaluation E t ht ζ Z X :=
  K0WithSupport.lift_mk Z (tensorCubeEvaluation E t ht ζ Z)
    (tensorCubeEvaluation_iso E t ht ζ Z) (tensorCubeEvaluation_triangle E t ht ζ Z hζ) X

@[simp]
lemma cyclicThreeValue_mk_concrete (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    cyclicThreeValue E t ht ζ hζ Z (K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) =
      tensorCubeClass E t ht ζ P Z hp hs := cyclicThreeValue_mk E t ht ζ hζ Z _

/-- Extend the additive cubic value to an E-linear endomorphism. -/
def cyclicThree : K0WithSupport.Coefficients E Z →ₗ[E] K0WithSupport.Coefficients E Z :=
  coefficientLinearExtension E (cyclicThreeValue E t ht ζ hζ Z)

@[simp]
lemma cyclicThree_tmul (a : E) (x : K0WithSupport Z) :
    cyclicThree E t ht ζ hζ Z (a ⊗ₜ[ℤ] x) = a • cyclicThreeValue E t ht ζ hζ Z x :=
  coefficientLinearExtension_tmul E _ a x

@[simp]
lemma cyclicThree_tmul_mk (a : E) (X : SupportedPerfectHomotopyOn Z) :
    cyclicThree E t ht ζ hζ Z (a ⊗ₜ[ℤ] K0WithSupport.mk Z X) =
      a • tensorCubeEvaluation E t ht ζ Z X := by
  rw [cyclicThree_tmul, cyclicThreeValue_mk]

lemma cyclicThree_mk_concrete (a : E) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    cyclicThree E t ht ζ hζ Z (a ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) =
      a • tensorCubeClass E t ht ζ P Z hp hs := cyclicThree_tmul_mk E t ht ζ hζ Z a _

lemma cyclicThreeValue_unique (F : K0WithSupport Z →+ K0WithSupport.Coefficients E Z)
    (hF : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P),
      F (K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) =
        tensorCubeClass E t ht ζ P Z hp hs) :
    F = cyclicThreeValue E t ht ζ hζ Z := by
  apply K0WithSupport.hom_ext
  intro X
  rw [cyclicThreeValue_mk]
  exact hF (supportedPerfectRepresentative X) (supportedPerfectRepresentative_perfect X)
    (supportedPerfectRepresentative_support X)

lemma cyclicThree_unique
    (F : K0WithSupport.Coefficients E Z →ₗ[E] K0WithSupport.Coefficients E Z)
    (hF : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P),
      F ((1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) =
        tensorCubeClass E t ht ζ P Z hp hs) : F = cyclicThree E t ht ζ hζ Z := by
  let G : K0WithSupport Z →+ K0WithSupport.Coefficients E Z := {
    toFun := fun x => F ((1 : E) ⊗ₜ[ℤ] x)
    map_zero' := by rw [TensorProduct.tmul_zero, map_zero]
    map_add' := by intro x y; rw [TensorProduct.tmul_add, map_add] }
  have hG : G = cyclicThreeValue E t ht ζ hζ Z :=
    cyclicThreeValue_unique E t ht ζ hζ Z G hF
  apply coefficientLinearExtension_unique
  intro x
  exact congrArg (fun g : K0WithSupport Z →+ K0WithSupport.Coefficients E Z => g x) hG

end Adams
end SerrePositivity
