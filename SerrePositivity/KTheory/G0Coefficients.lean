module

public import SerrePositivity.KTheory.G0Functoriality
public import SerrePositivity.KTheory.CoefficientExtension

/-! # Coefficients and support enlargement for supported G₀ -/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity
open scoped TensorProduct
variable (E : Type v) [CommRing E]
variable {R : Type u} [CommRing R] (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

namespace G0WithSupport
abbrev Coefficients := E ⊗[ℤ] G0WithSupport Z

/-- Coefficient extension of the support enlargement map. -/
def coefficientEnlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    Coefficients E Z →ₗ[E] Coefficients E W := g0CoefficientMap E (enlarge h)

@[simp] lemma coefficientEnlarge_tmul {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (a : E) (x : G0WithSupport Z) :
    coefficientEnlarge E h (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] enlarge h x := rfl

lemma coefficientEnlarge_comp {Z W V : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (h' : W ≤ V) :
    (coefficientEnlarge E h').comp (coefficientEnlarge E h) =
      coefficientEnlarge E (h.trans h') := by
  rw [coefficientEnlarge, coefficientEnlarge, g0CoefficientMap_comp, enlarge_comp]
  rfl

end G0WithSupport
end SerrePositivity
