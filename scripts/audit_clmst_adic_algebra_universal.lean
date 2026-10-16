import SerrePositivity.CommutativeAlgebra.AdicCompletionAlgebraUniversal
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.adicCompletionToCompleteAlgebra
assert_no_sorry SerrePositivity.adicCompletionToCompleteAlgebra_of
assert_no_sorry SerrePositivity.adicCompletion_algHom_ext
assert_no_sorry SerrePositivity.adicCompletion_existsUnique_algHom

#print axioms SerrePositivity.adicCompletionToCompleteAlgebra
#print axioms SerrePositivity.adicCompletionToCompleteAlgebra_of
#print axioms SerrePositivity.adicCompletion_algHom_ext
#print axioms SerrePositivity.adicCompletion_existsUnique_algHom

noncomputable section
universe u v
open SerrePositivity
variable (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    (A : Type v) [CommRing A] [Algebra R A] [IsAdicComplete I A]

-- No separation or regularity is required on the source ring.
example : ∃! _f : AdicCompletion I R →ₐ[R] A, True :=
  adicCompletion_existsUnique_algHom R I hI A

example (r : R) :
    adicCompletionToCompleteAlgebra R I hI A (algebraMap R (AdicCompletion I R) r) =
      algebraMap R A r := adicCompletionToCompleteAlgebra_of R I hI A r
