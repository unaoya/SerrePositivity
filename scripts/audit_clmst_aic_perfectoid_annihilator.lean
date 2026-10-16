import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedPerfectoidQuotient
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.aicPerfectoid_quotient_of_radical_and_complete
assert_no_sorry SerrePositivity.annihilatorPrincipalQuotient_isAdicComplete
assert_no_sorry SerrePositivity.annihilatorPrincipal_isRadical_of_reduced
assert_no_sorry SerrePositivity.aicPerfectoid_annihilatorPrincipalQuotient
#print axioms SerrePositivity.aicPerfectoid_quotient_of_radical_and_complete
#print axioms SerrePositivity.annihilatorPrincipalQuotient_isAdicComplete
#print axioms SerrePositivity.annihilatorPrincipal_isRadical_of_reduced
#print axioms SerrePositivity.aicPerfectoid_annihilatorPrincipalQuotient

noncomputable section
universe u
open SerrePositivity
set_option backward.isDefEq.respectTransparency false

-- The actual perfectoid test quotient uses exactly the original scalar annihilator.
theorem audit_actual_annihilator_perfectoid_quotient
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R) :
    IsIntegralPerfectoid (R ⧸ (Ideal.span {g}).annihilator) p ∧
      ∀ x : R, Ideal.Quotient.mk (Ideal.span {g}).annihilator x = 0 ↔ g * x = 0 := by
  refine ⟨aicPerfectoid_annihilatorPrincipalQuotient R p hR hAIC g, ?_⟩
  intro x
  rw [Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_annihilator_span_singleton]
  change x * g = 0 ↔ g * x = 0
  rw [mul_comm]

-- Zero and unit scalars keep the expected quotient maps, including a zero original ring.
theorem audit_annihilator_quotient_zero_and_unit
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (hAIC : IsAbsolutelyIntegrallyClosed R) :
    IsIntegralPerfectoid (R ⧸ (Ideal.span {(0 : R)}).annihilator) p ∧
      IsIntegralPerfectoid (R ⧸ (Ideal.span {(1 : R)}).annihilator) p ∧
      Subsingleton (R ⧸ (Ideal.span {(0 : R)}).annihilator) ∧
      Function.Injective (Ideal.Quotient.mk (Ideal.span {(1 : R)}).annihilator) := by
  have hzero : (Ideal.span {(0 : R)}).annihilator = ⊤ := by
    ext x
    simp only [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_zero,
      Submodule.mem_top]
  have hone : (Ideal.span {(1 : R)}).annihilator = ⊥ := by
    ext x
    simp only [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_one,
      Ideal.mem_bot]
  refine ⟨aicPerfectoid_annihilatorPrincipalQuotient R p hR hAIC 0,
    aicPerfectoid_annihilatorPrincipalQuotient R p hR hAIC 1, ?_, ?_⟩
  · rw [hzero]
    infer_instance
  · apply (RingHom.injective_iff_ker_eq_bot _).mpr
    rw [Ideal.mk_ker, hone]

assert_no_sorry audit_actual_annihilator_perfectoid_quotient
assert_no_sorry audit_annihilator_quotient_zero_and_unit
#print axioms audit_actual_annihilator_perfectoid_quotient
#print axioms audit_annihilator_quotient_zero_and_unit
