import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor
import SerrePositivity.BhattScholze.QuotientPerfectoidization
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.IsPerfectoidization.lift
assert_no_sorry SerrePositivity.IsPerfectoidization.lift_comp
assert_no_sorry SerrePositivity.IsPerfectoidization.lift_unique
assert_no_sorry SerrePositivity.IsPerfectoidization.map
assert_no_sorry SerrePositivity.IsPerfectoidization.map_comp
assert_no_sorry SerrePositivity.IsPerfectoidization.map_id
assert_no_sorry SerrePositivity.IsPerfectoidization.map_map
assert_no_sorry SerrePositivity.IsPerfectoidization.exists_equiv
assert_no_sorry SerrePositivity.IsPerfectoidization.surjective_iff
assert_no_sorry SerrePositivity.IsPerfectoidization.ker_eq
assert_no_sorry SerrePositivity.IsPerfectoidization.ker_comp_eq

assert_no_sorry SerrePositivity.QuotientPerfectoidization
assert_no_sorry SerrePositivity.toQuotientPerfectoidization
assert_no_sorry SerrePositivity.isPerfectoidization_toQuotientPerfectoidization
assert_no_sorry SerrePositivity.algebraMap_quotientPerfectoidization
assert_no_sorry SerrePositivity.algebraMap_base_quotientPerfectoidization
assert_no_sorry SerrePositivity.quotientPerfectoidization_subsingleton
assert_no_sorry SerrePositivity.quotientPerfectoidization_natCast_eq_zero

open SerrePositivity

-- Arbitrary ideals, without finiteness or completeness assumptions on the quotient.
example {R : Type} [CommRing R] (I : Ideal R) (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) :
    IsScalarTower R (R ⧸ I) (QuotientPerfectoidization R I p hR) := inferInstance

example {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) :
    IsPerfectoidization p (toQuotientPerfectoidization R (Ideal.span {0}) p hR) :=
  isPerfectoidization_toQuotientPerfectoidization R _ p hR

example {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) (hg : IsUnit g) :
    Subsingleton (QuotientPerfectoidization R (Ideal.span {g}) p hR) := by
  let : Subsingleton (R ⧸ Ideal.span {g}) := by
    rw [Ideal.span_singleton_eq_top.mpr hg]
    infer_instance
  exact quotientPerfectoidization_subsingleton R _ p hR

example {R : Type} [CommRing R] [Subsingleton R] (p : ℕ) [Fact p.Prime]
    (I : Ideal R) :
    Subsingleton (QuotientPerfectoidization R I p (Or.inl inferInstance)) :=
  quotientPerfectoidization_subsingleton R I p _

example {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) :
    (p : QuotientPerfectoidization R (Ideal.span {(p : R)}) p hR) = 0 :=
  quotientPerfectoidization_natCast_eq_zero R _ p hR (Ideal.mem_span_singleton_self _)
