import SerrePositivity.CLMST.Prop247BaseChange
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CLMST.prop247_completion_unit_surjective
assert_no_sorry SerrePositivity.CLMST.prop247_tensor_completion_unit_surjective
assert_no_sorry SerrePositivity.CLMST.prop247_completionMap
assert_no_sorry SerrePositivity.CLMST.prop247_completionMap_unit
assert_no_sorry SerrePositivity.CLMST.prop247_completion_square
assert_no_sorry SerrePositivity.CLMST.prop247_completion_cone_bound
#print axioms SerrePositivity.CLMST.prop247_completion_unit_surjective
#print axioms SerrePositivity.CLMST.prop247_tensor_completion_unit_surjective
#print axioms SerrePositivity.CLMST.prop247_completionMap
#print axioms SerrePositivity.CLMST.prop247_completionMap_unit
#print axioms SerrePositivity.CLMST.prop247_completion_square
#print axioms SerrePositivity.CLMST.prop247_completion_cone_bound

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST
open scoped TensorProduct

-- The actual standard completion map of the original base-changed algebra;
-- no flatness or regularity is hidden in the source-surjectivity step.
theorem audit_prop247_original_tensor_unit
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hB : IsIntegralPerfectoid B p)
    (x : AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S)) :
    ∃ y : B ⊗[R] S, algebraMap (B ⊗[R] S) _ y = x :=
  prop247_tensor_completion_unit_surjective B p R S hB x

-- The square retains every coefficient b of the original B action.
theorem audit_prop247_completion_coefficient
    (B L C T : Type u) [CommRing B] [CommRing L] [CommRing C] [CommRing T]
    [Algebra B L] [Algebra B C] [Algebra B T]
    (p : ℕ) [Fact p.Prime] (β : L →ₐ[B] C)
    (hβ : IsPerfectoidization p β.toRingHom) (e : C ≃ₐ[B] T) (b : B) :
    e (prop247_completionMap p β hβ
      (algebraMap L (AdicCompletion (Ideal.span {(p : L)}) L) (algebraMap B L b))) =
      algebraMap B T b := by
  rw [prop247_completionMap_unit, β.commutes, e.commutes]

assert_no_sorry audit_prop247_original_tensor_unit
assert_no_sorry audit_prop247_completion_coefficient
#print axioms audit_prop247_original_tensor_unit
#print axioms audit_prop247_completion_coefficient
