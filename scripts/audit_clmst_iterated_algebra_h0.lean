import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedAlgebraH0Comparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.iteratedAlgebraCompletionH0PDAlgEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedAlgebraCompletionH0PDAlgEquiv_unit
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedCompletedTensorH0PDAlgEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedCompletedTensorH0PDAlgEquiv_unit
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedCompletedTensorH0PDAlgEquiv_algebraMap

#print axioms SerrePositivity.DerivedCompletion.iteratedAlgebraCompletionH0PDAlgEquiv
#print axioms SerrePositivity.DerivedCompletion.iteratedAlgebraCompletionH0PDAlgEquiv_unit
#print axioms SerrePositivity.DerivedCompletion.iteratedCompletedTensorH0PDAlgEquiv
#print axioms SerrePositivity.DerivedCompletion.iteratedCompletedTensorH0PDAlgEquiv_unit
#print axioms SerrePositivity.DerivedCompletion.iteratedCompletedTensorH0PDAlgEquiv_algebraMap

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

-- The first coordinate need not be prime or regular.
example (d : R) :
    let A0 := boundedAboveCompletedTensorAlgebra R ((0 : ℕ) : R) S T
    let B := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A0.X.obj
    letI := derivedH0CommRing A0
    letI := derivedH0Algebra A0
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj A0)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj A0)
    letI := completionH0ScalarAlgebra R d A0
    letI := pdCompletionCommRing B 0 (algebraMap R B d)
    letI := pdCompletionAlgebra B 0 (algebraMap R B d)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R d).obj A0).X.obj ≃ₐ[B]
      PDCompletionH0 B 0 (algebraMap R B d) :=
  iteratedCompletedTensorH0PDAlgEquiv R 0 d S T

-- The second coordinate need not be regular.
example (p : ℕ) :
    let A0 := boundedAboveCompletedTensorAlgebra R (p : R) S T
    let B := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A0.X.obj
    letI := derivedH0CommRing A0
    letI := derivedH0Algebra A0
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R 0).obj A0)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R 0).obj A0)
    letI := completionH0ScalarAlgebra R 0 A0
    letI := pdCompletionCommRing B p (algebraMap R B 0)
    letI := pdCompletionAlgebra B p (algebraMap R B 0)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R 0).obj A0).X.obj ≃ₐ[B]
      PDCompletionH0 B p (algebraMap R B 0) :=
  iteratedCompletedTensorH0PDAlgEquiv R p 0 S T
