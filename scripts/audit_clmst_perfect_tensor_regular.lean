import SerrePositivity.BhattScholze.PerfectDeltaTensorRegular
import SerrePositivity.BhattScholze.PerfectOrientedPrism
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.tensor_p_mul_injective_of_perfect_residue
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_tensor_p_mul_injective
#print axioms SerrePositivity.tensor_p_mul_injective_of_perfect_residue
#print axioms SerrePositivity.BhattScholze.perfectDelta_tensor_p_mul_injective

noncomputable section
universe u
open scoped TensorProduct
open SerrePositivity SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

-- Neither completion nor flatness is required for the ordinary tensor conclusion.
example
    [PerfectRing (R ⧸ Ideal.span {(p : R)}) p]
    [PerfectRing (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {(p : R)})) p]
    [PerfectRing (T ⧸ Ideal.map (algebraMap R T) (Ideal.span {(p : R)})) p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    Function.Injective (fun x : S ⊗[R] T => (p : S ⊗[R] T) * x) :=
  tensor_p_mul_injective_of_perfect_residue p R S T ha hS hT

example (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect) :
    Function.Injective (fun x : S ⊗[R] T => (p : S ⊗[R] T) * x) :=
  perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT

-- The original complete prism diagram is a special case, with no extra hypotheses.
example (P : OrientedPrism p R) (Q : OrientedPrism p S) (U : OrientedPrism p T)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    (hU : U.deltaStructure.IsPerfect) :
    Function.Injective (fun x : S ⊗[R] T => (p : S ⊗[R] T) * x) :=
  perfectDelta_tensor_p_mul_injective p R S T P.deltaStructure Q.deltaStructure U.deltaStructure
    hP hQ hU
