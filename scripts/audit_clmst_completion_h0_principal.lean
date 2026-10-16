import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0PrincipalComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.completionH0ScalarAlgebra
assert_no_sorry SerrePositivity.DerivedCompletion.completionH0ScalarTower
assert_no_sorry SerrePositivity.DerivedCompletion.completionH0_isModuleComplete_scalar
assert_no_sorry SerrePositivity.DerivedCompletion.completionH0PrincipalAlgEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.completionH0PrincipalAlgEquiv_unit
assert_no_sorry SerrePositivity.DerivedCompletion.completionH0PairAlgEquivOfCompleteFirst
assert_no_sorry SerrePositivity.DerivedCompletion.completionH0PairAlgEquivOfCompleteFirst_unit

#print axioms SerrePositivity.DerivedCompletion.completionH0ScalarAlgebra
#print axioms SerrePositivity.DerivedCompletion.completionH0ScalarTower
#print axioms SerrePositivity.DerivedCompletion.completionH0_isModuleComplete_scalar
#print axioms SerrePositivity.DerivedCompletion.completionH0PrincipalAlgEquiv
#print axioms SerrePositivity.DerivedCompletion.completionH0PrincipalAlgEquiv_unit
#print axioms SerrePositivity.DerivedCompletion.completionH0PairAlgEquivOfCompleteFirst
#print axioms SerrePositivity.DerivedCompletion.completionH0PairAlgEquivOfCompleteFirst_unit

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p d : R)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))) [A.X.obj.IsLE 0]

-- The coefficient completeness needed by the pair comparison is automatic
-- for the original first completion; no extra completeness assumption is added.
example :
    let A0 := (boundedAboveCompletionCommMonFunctor R p).obj A
    let B := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A0.X.obj
    letI := derivedH0CommRing A0
    letI := derivedH0Algebra A0
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj A0)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj A0)
    letI := completionH0ScalarAlgebra R d A0
    letI := pairCompletionCommRing B (algebraMap R B p) (algebraMap R B d)
    letI := pairCompletionAlgebra B (algebraMap R B p) (algebraMap R B d)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R d).obj A0).X.obj ≃ₐ[B]
      PairCompletionH0 B (algebraMap R B p) (algebraMap R B d) := by
  let A0 := (boundedAboveCompletionCommMonFunctor R p).obj A
  let hle : A0.X.obj.IsLE 0 :=
    boundedAboveDerivedCompletionFunctor_isLE R p A.X 0 inferInstance
  exact completionH0PairAlgEquivOfCompleteFirst R d A0 p
    (derivedComplexCompletionFunctor_homology_isModuleComplete R p A.X.obj 0)

-- Zero coordinates are allowed; regularity is not part of this H⁰ comparison.
example :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R 0).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R 0).obj A)
    letI := completionH0ScalarAlgebra R 0 A
    let B := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
    letI := principalCompletionCommRing B (algebraMap R B 0)
    letI := principalCompletionAlgebra B (algebraMap R B 0)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R 0).obj A).X.obj ≃ₐ[B]
      PrincipalCompletionH0 B (algebraMap R B 0) :=
  completionH0PrincipalAlgEquiv R 0 A
