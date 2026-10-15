module

public import SerrePositivity.KTheory.Adams.Family
public import SerrePositivity.KTheory.Adams.WeightPolynomial

/-! # Polynomial Adams operations commute with enlargement of support -/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.Adams
open Polynomial
variable {R : Type u} [CommRing R] {E : Type v} [CommRing E] {p : ℕ}

lemma SupportedAdams.polynomial_enlarge (A : SupportedAdams R E p)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) (Q : E[X])
    (x : K0WithSupport.Coefficients E Z) :
    (aeval (A.operation W) Q) (K0WithSupport.coefficientEnlarge E h x) =
      K0WithSupport.coefficientEnlarge E h ((aeval (A.operation Z) Q) x) :=
  (polynomial_intertwine _ _ (K0WithSupport.coefficientEnlarge E h)
    (fun y => (A.enlarge h y).symm) Q x).symm

end SerrePositivity.Adams
