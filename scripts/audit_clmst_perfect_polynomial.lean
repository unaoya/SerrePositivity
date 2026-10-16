import SerrePositivity.CommutativeAlgebra.PerfectPolynomialFlat
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

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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

assert_no_sorry SerrePositivity.perfectPolynomialStage
assert_no_sorry SerrePositivity.perfectPolynomialStage_frobenius
assert_no_sorry SerrePositivity.perfectPolynomial_of_injective
assert_no_sorry SerrePositivity.perfectPolynomialStage_injective
assert_no_sorry SerrePositivity.perfectPolynomialStep
assert_no_sorry SerrePositivity.perfectPolynomialStage_step
assert_no_sorry SerrePositivity.perfectPolynomialTransition
assert_no_sorry SerrePositivity.perfectPolynomialDirectedSystem
assert_no_sorry SerrePositivity.perfectPolynomialStage_transition
assert_no_sorry SerrePositivity.perfectPolynomialStage_jointly_surjective
assert_no_sorry SerrePositivity.perfectPolynomialLimitMap
assert_no_sorry SerrePositivity.perfectPolynomialLimitMap_bijective
assert_no_sorry SerrePositivity.perfectPolynomialLimitEquiv
assert_no_sorry SerrePositivity.perfectPolynomial_flat

#print axioms SerrePositivity.perfectPolynomialStage
#print axioms SerrePositivity.perfectPolynomialStage_frobenius
#print axioms SerrePositivity.perfectPolynomial_of_injective
#print axioms SerrePositivity.perfectPolynomialStage_injective
#print axioms SerrePositivity.perfectPolynomialStep
#print axioms SerrePositivity.perfectPolynomialStage_step
#print axioms SerrePositivity.perfectPolynomialTransition
#print axioms SerrePositivity.perfectPolynomialDirectedSystem
#print axioms SerrePositivity.perfectPolynomialStage_transition
#print axioms SerrePositivity.perfectPolynomialStage_jointly_surjective
#print axioms SerrePositivity.perfectPolynomialLimitMap
#print axioms SerrePositivity.perfectPolynomialLimitMap_bijective
#print axioms SerrePositivity.perfectPolynomialLimitEquiv
#print axioms SerrePositivity.perfectPolynomial_flat

variable [PerfectRing R p]

example : Module.Flat R (PerfectPolynomial p R σ) := perfectPolynomial_flat p R σ

example : Module.DirectLimit (fun _ : ℕ => MvPolynomial σ R)
    (perfectPolynomialTransition p R σ) ≃ₗ[R] PerfectPolynomial p R σ :=
  perfectPolynomialLimitEquiv p R σ

-- Each transition fixes coefficients, rather than applying Frobenius to R.
example (r : R) : perfectPolynomialStep p R σ (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.aeval_C _ r

example (n : ℕ) (f : MvPolynomial σ R) :
    perfectPolynomialLimitEquiv p R σ
      (Module.DirectLimit.of R ℕ (fun _ : ℕ => MvPolynomial σ R)
        (perfectPolynomialTransition p R σ) n f) = perfectPolynomialStage p R σ n f :=
  by
    change perfectPolynomialLimitMap p R σ _ = _
    exact Module.DirectLimit.lift_of (R := R) (ι := ℕ)
      (G := fun _ : ℕ => MvPolynomial σ R) (f := perfectPolynomialTransition p R σ)
      (g := fun n => (perfectPolynomialStage p R σ n).toLinearMap)
      (Hg := perfectPolynomialStage_transition p R σ) f
