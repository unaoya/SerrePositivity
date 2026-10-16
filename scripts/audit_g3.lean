import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion
import Mathlib.Util.AssertNoSorry

open SerrePositivity
open scoped TensorProduct

assert_no_sorry SerrePositivity.isResolutionOf_baseChange_of_torVanishing
#print axioms SerrePositivity.isResolutionOf_baseChange_of_torVanishing
assert_no_sorry SerrePositivity.scalarExtensionTensorCancelIso
#print axioms SerrePositivity.scalarExtensionTensorCancelIso
assert_no_sorry SerrePositivity.torAcyclicBaseChangeIso
#print axioms SerrePositivity.torAcyclicBaseChangeIso
assert_no_sorry SerrePositivity.tor_isZero_of_acyclicBaseChange_flat
#print axioms SerrePositivity.tor_isZero_of_acyclicBaseChange_flat
assert_no_sorry SerrePositivity.quotientTensorReductionEquiv
#print axioms SerrePositivity.quotientTensorReductionEquiv
assert_no_sorry SerrePositivity.isCompletelyFlat_of_acyclic_flat_reduction
#print axioms SerrePositivity.isCompletelyFlat_of_acyclic_flat_reduction
assert_no_sorry SerrePositivity.isCompletelyFlat_principal_of_regular
#print axioms SerrePositivity.isCompletelyFlat_principal_of_regular
assert_no_sorry SerrePositivity.isCompletelyFaithfullyFlat_principal_of_regular
#print axioms SerrePositivity.isCompletelyFaithfullyFlat_principal_of_regular

-- Exact requested G3 hypotheses: no completeness, finiteness, or Noetherian assumption.
example {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (hR : Function.Injective (fun r : R ↦ a * r))
    (hM : Function.Injective (fun m : M ↦ a • m))
    (hF : Module.Flat (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⊗[R] M)) :
    IsCompletelyFlat (Ideal.span {a}) M :=
  isCompletelyFlat_principal_of_regular a hR M hM hF

-- Faithful flatness is exactly the existing residue condition, with no added ring flatness.
example {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (hR : IsSMulRegular R a) (hM : IsSMulRegular M a)
    (hF : Module.FaithfullyFlat (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⊗[R] M)) :
    IsCompletelyFaithfullyFlat (Ideal.span {a}) M :=
  isCompletelyFaithfullyFlat_principal_of_regular a hR M hM hF

-- The unit ideal and its zero residue ring require no extra exclusions.
example {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (hF : Module.Flat (R ⧸ Ideal.span {(1 : R)})
      ((R ⧸ Ideal.span {(1 : R)}) ⊗[R] M)) :
    IsCompletelyFlat (Ideal.span {(1 : R)}) M :=
  isCompletelyFlat_principal_of_regular 1 (by simp)
    M (by simp) hF
