import SerrePositivity.CommutativeAlgebra.CoefficientTensorAutomorphism
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.coefficientTensorEndomorphism
assert_no_sorry SerrePositivity.coefficientTensorEndomorphism_tmul
assert_no_sorry SerrePositivity.coefficientTensorAutomorphism_inverse_compat
assert_no_sorry SerrePositivity.coefficientTensorAutomorphism
assert_no_sorry SerrePositivity.coefficientTensorAutomorphism_tmul
assert_no_sorry SerrePositivity.coefficientTensorAutomorphism_symm_tmul

#print axioms SerrePositivity.coefficientTensorEndomorphism
#print axioms SerrePositivity.coefficientTensorEndomorphism_tmul
#print axioms SerrePositivity.coefficientTensorAutomorphism_inverse_compat
#print axioms SerrePositivity.coefficientTensorAutomorphism
#print axioms SerrePositivity.coefficientTensorAutomorphism_tmul
#print axioms SerrePositivity.coefficientTensorAutomorphism_symm_tmul

noncomputable section
universe u v w
open SerrePositivity
open scoped TensorProduct
variable (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (eR : R ≃+* R) (eS : S ≃+* S) (eT : T ≃+* T)
    (hS : ∀ r, eS (algebraMap R S r) = algebraMap R S (eR r))
    (hT : ∀ r, eT (algebraMap R T r) = algebraMap R T (eR r))

-- Independent universes and an arbitrary coefficient automorphism are retained.
example : S ⊗[R] T ≃+* S ⊗[R] T := coefficientTensorAutomorphism eR eS eT hS hT

example (s : S) (t : T) :
    (coefficientTensorAutomorphism eR eS eT hS hT).symm (s ⊗ₜ[R] t) =
      eS.symm s ⊗ₜ[R] eT.symm t :=
  coefficientTensorAutomorphism_symm_tmul eR eS eT hS hT s t

example (z : S ⊗[R] T) :
    (coefficientTensorAutomorphism eR eS eT hS hT).symm
      (coefficientTensorAutomorphism eR eS eT hS hT z) = z :=
  (coefficientTensorAutomorphism eR eS eT hS hT).symm_apply_apply z
