import SerrePositivity.BhattScholze.PerfectoidizationSurjectiveMap
import SerrePositivity.BhattScholze.QuotientPerfectoidization
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.isAdicComplete_ringHom_range
assert_no_sorry SerrePositivity.BhattScholze.perfectoidization_map_surjective_of_surjective
#print axioms SerrePositivity.isAdicComplete_ringHom_range
#print axioms SerrePositivity.BhattScholze.perfectoidization_map_surjective_of_surjective

noncomputable section
universe u
open SerrePositivity SerrePositivity.BhattScholze

-- An arbitrary B3 quotient, with no separatedness or completeness of R/J.
theorem audit_b3_arbitrary_quotient_composite_surjective
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (J : Ideal R) :
    Function.Surjective ((toQuotientPerfectoidization R J p hR).comp
      (Ideal.Quotient.mk J)) := by
  have hf : IsPerfectoidization p (RingHom.id R) := by
    refine ⟨hR, ?_⟩
    intro T _ _ k
    refine ⟨k, RingHom.comp_id k, ?_⟩
    intro l hl
    simpa only [RingHom.comp_id] using hl
  let hg := isPerfectoidization_toQuotientPerfectoidization R J p hR
  have h := perfectoidization_map_surjective_of_surjective hf hg
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have he := hf.map_comp hg (Ideal.Quotient.mk J)
  simpa only [RingHom.comp_id] using he ▸ h

-- This includes the zero ring and the unit ideal without nontriviality assumptions.
theorem audit_b3_arbitrary_quotient_unit_surjective
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (J : Ideal R) :
    Function.Surjective (toQuotientPerfectoidization R J p hR) := by
  intro x
  obtain ⟨r, hr⟩ := audit_b3_arbitrary_quotient_composite_surjective R p hR J x
  exact ⟨Ideal.Quotient.mk J r, hr⟩

assert_no_sorry audit_b3_arbitrary_quotient_composite_surjective
assert_no_sorry audit_b3_arbitrary_quotient_unit_surjective
#print axioms audit_b3_arbitrary_quotient_unit_surjective
