import SerrePositivity.BhattScholze.PerfectDeltaCompletedTensorDiscrete
import SerrePositivity.BhattScholze.PerfectOrientedPrism
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaAlgebra_p_regular
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaAlgebra_perfectRing_residue
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedTensor_pure
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedTensorH0_p_mul_injective
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedTensorH0_isAdicComplete

#print axioms SerrePositivity.BhattScholze.perfectDeltaAlgebra_p_regular
#print axioms SerrePositivity.BhattScholze.perfectDeltaAlgebra_perfectRing_residue
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedTensor_pure
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedTensorH0_p_mul_injective
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedTensorH0_isAdicComplete

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (P : OrientedPrism p R) (Q : OrientedPrism p S) (U : OrientedPrism p T)

-- The actual prism inputs supply all regularity and perfect-residue hypotheses.
-- No flatness, nontriviality or separate Tor hypothesis is added.
example (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    (hU : U.deltaStructure.IsPerfect) :
    let X := (boundedAboveCompletedTensorAlgebra R (p : R) S T).X
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => (p : R) • x) :=
  perfectDelta_completedTensor_pure p R S T P.deltaStructure Q.deltaStructure U.deltaStructure
    hP hQ hU

example (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    (hU : U.deltaStructure.IsPerfect) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    letI := derivedH0CommRing A
    Function.Injective (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj =>
      (p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) * x) :=
  perfectDelta_completedTensorH0_p_mul_injective p R S T
    P.deltaStructure Q.deltaStructure U.deltaStructure hP hQ hU

example (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    (hU : U.deltaStructure.IsPerfect) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    letI := derivedH0CommRing A
    IsAdicComplete (Ideal.span {(p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)})
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :=
  perfectDelta_completedTensorH0_isAdicComplete p R S T
    P.deltaStructure Q.deltaStructure U.deltaStructure hP hQ hU
