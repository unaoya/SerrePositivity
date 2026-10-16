import SerrePositivity.CommutativeAlgebra.PerfectPolynomial
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.PerfectPolynomial
assert_no_sorry SerrePositivity.perfectPolynomialAlgebra
assert_no_sorry SerrePositivity.perfectClosure_lift_of
assert_no_sorry SerrePositivity.perfectPolynomialEval
assert_no_sorry SerrePositivity.perfectPolynomialEval_X
assert_no_sorry SerrePositivity.perfectPolynomialEval_surjective
assert_no_sorry SerrePositivity.perfectPolynomial_hom_ext
assert_no_sorry SerrePositivity.perfectPolynomialHomEquiv

#print axioms SerrePositivity.PerfectPolynomial
#print axioms SerrePositivity.perfectPolynomialAlgebra
#print axioms SerrePositivity.perfectClosure_lift_of
#print axioms SerrePositivity.perfectPolynomialEval
#print axioms SerrePositivity.perfectPolynomialEval_X
#print axioms SerrePositivity.perfectPolynomialEval_surjective
#print axioms SerrePositivity.perfectPolynomial_hom_ext
#print axioms SerrePositivity.perfectPolynomialHomEquiv

noncomputable section
universe u
open SerrePositivity
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]
    (σ S : Type u) [CommRing S] [Algebra R S] [CharP S p] [PerfectRing S p]

-- No perfectness hypothesis on R and no finiteness hypothesis on σ or S.
example : (σ → S) ≃ (PerfectPolynomial p R σ →ₐ[R] S) :=
  perfectPolynomialHomEquiv p R σ S

example : Function.Surjective (perfectPolynomialEval p R S S id) :=
  perfectPolynomialEval_surjective p R S

example : PerfectRing (PerfectPolynomial p R σ) p := inferInstance
example : CharP (PerfectPolynomial p R σ) p := inferInstance

-- The unique map out of the empty-variable algebra is included.
example (f g : PerfectPolynomial p R PEmpty →ₐ[R] S) : f = g :=
  perfectPolynomial_hom_ext p R PEmpty S (fun x => nomatch x)
