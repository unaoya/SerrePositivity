import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedHenselian
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.monic_splits
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.lift_root_to_field
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.henselianLocalRing
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.standardEtale_hasMap_lift
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.standardEtale_point_lift
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.isStandardEtale_point_lift
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.etale_point_lift
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.monic_splits
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.lift_root_to_field
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.henselianLocalRing
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.standardEtale_hasMap_lift
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.standardEtale_point_lift
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.isStandardEtale_point_lift
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.etale_point_lift

noncomputable section
universe u
open SerrePositivity IsLocalRing

theorem audit_localized_aic_henselian
    (R : Type u) [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (p : Ideal R) [p.IsPrime] : HenselianLocalRing (Localization.AtPrime p) :=
  (hR.localization p.primeCompl (Localization.AtPrime p)).henselianLocalRing

theorem audit_aic_etale_section_surjective
    (R A : Type u) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R)
    (point : A →ₐ[R] ResidueField R) :
    ∃ l : A →ₐ[R] R, (Algebra.ofId R (ResidueField R)).comp l = point ∧
      Function.Surjective l := by
  obtain ⟨l, hl⟩ := hR.etale_point_lift point
  refine ⟨l, hl, ?_⟩
  intro r
  exact ⟨algebraMap R A r, by simpa only [Algebra.algebraMap_self, RingHom.id_apply] using l.commutes r⟩

assert_no_sorry audit_localized_aic_henselian
assert_no_sorry audit_aic_etale_section_surjective
#print axioms audit_localized_aic_henselian
#print axioms audit_aic_etale_section_surjective
