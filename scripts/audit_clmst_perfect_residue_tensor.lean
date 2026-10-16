import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PerfectResidueCompletedTensor
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.completedTensor_pure_of_perfect_residue
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorAlgebra_pure_of_perfect_residue
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0_p_mul_injective_of_perfect_residue
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0_isAdicComplete_of_perfect_residue

#print axioms SerrePositivity.DerivedCompletion.completedTensor_pure_of_perfect_residue
#print axioms SerrePositivity.DerivedCompletion.completedTensorAlgebra_pure_of_perfect_residue
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0_p_mul_injective_of_perfect_residue
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0_isAdicComplete_of_perfect_residue

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

-- No flatness hypothesis on the residue tensor or on either algebra map.
example
    [PerfectRing (R ⧸ Ideal.span {(p : R)}) p]
    [PerfectRing (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {(p : R)})) p]
    [PerfectRing (T ⧸ Ideal.map (algebraMap R T) (Ideal.span {(p : R)})) p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    let X := (boundedAboveCompletedTensorAlgebra R (p : R) S T).X
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => (p : R) • x) :=
  completedTensorAlgebra_pure_of_perfect_residue p R S T ha hS hT

example
    [PerfectRing (R ⧸ Ideal.span {(p : R)}) p]
    [PerfectRing (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {(p : R)})) p]
    [PerfectRing (T ⧸ Ideal.map (algebraMap R T) (Ideal.span {(p : R)})) p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    letI := derivedH0CommRing A
    IsAdicComplete (Ideal.span {(p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)})
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :=
  completedTensorH0_isAdicComplete_of_perfect_residue p R S T ha hS hT
