import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorClassicalComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0AdicRingEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0AdicRingEquiv_unit
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0AdicRingEquiv_left
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0AdicRingEquiv_right

#print axioms SerrePositivity.DerivedCompletion.completedTensorH0AdicRingEquiv
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0AdicRingEquiv_unit
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0AdicRingEquiv_left
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0AdicRingEquiv_right

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hB : IsSMulRegular (S ⊗[R] T) (p : S ⊗[R] T))

-- Only regularity of the original ordinary tensor is required, without flatness or perfectness.
example :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃+*
        AdicCompletion (Ideal.span {(p : S ⊗[R] T)}) (S ⊗[R] T) :=
  completedTensorH0AdicRingEquiv R p S T hB

example (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      algebraMap (S ⊗[R] T) (AdicCompletion (Ideal.span {(p : S ⊗[R] T)}) (S ⊗[R] T))
        (derivedTensorH0AlgEquiv S T x) :=
  completedTensorH0AdicRingEquiv_unit R p S T hB x

assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0AdicRingEquiv_algebraMap
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0AdicRingEquiv_algebraMap
