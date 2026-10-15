import SerrePositivity.KTheory.MaximalSupportCoefficientLength
import SerrePositivity.KTheory.Adams.CoefficientLengthEquiv
import SerrePositivity.KTheory.LocalizationCoefficients
import Mathlib.Util.AssertNoSorry

open SerrePositivity
noncomputable section
universe u v
example (E : Type v) [CommRing E] {R : Type u} [CommRing R] [IsNoetherianRing R]
    (W : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hw : ∀ p ∈ W, p.asIdeal.IsMaximal) [Fintype {p : PrimeSpectrum R // p ∈ W}] :
    G0WithSupport.Coefficients E W ≃ₗ[E] ({p : PrimeSpectrum R // p ∈ W} → E) :=
  Adams.coefficientG0LengthEquiv E W hw

assert_no_sorry SerrePositivity.G0WithSupport.coefficientEnlarge
assert_no_sorry SerrePositivity.G0WithSupport.coefficientEnlarge_comp
assert_no_sorry SerrePositivity.Adams.coefficientG0LengthEquiv
assert_no_sorry SerrePositivity.Adams.coefficientG0LengthEquiv_tmul
assert_no_sorry SerrePositivity.Adams.coefficientK0LengthEquiv
assert_no_sorry SerrePositivity.Adams.coefficient_eq_zero_of_localizations
assert_no_sorry SerrePositivity.G0WithSupport.coefficientLocalize_exact
#print axioms SerrePositivity.Adams.coefficientG0LengthEquiv
