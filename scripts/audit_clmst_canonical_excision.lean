import SerrePositivity.CLMST.PerfectoidizationExcisionComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.IsPerfectoidization.quotient_map
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedSideUnit
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedSideUnit_isPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedSideProjection
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedSideProjection_comp
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedSideProjection_eq_zero_of_mem
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedSideProjection_originalIdeal
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedComparison_ideal_le
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedComparison
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedComparison_square
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedComparison_unit
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationClosedComparison_eq_map
assert_no_sorry SerrePositivity.CLMST.perfectoidization_comparison_almost_of_canonical_excision
#print axioms SerrePositivity.IsPerfectoidization.quotient_map
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedSideUnit
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedSideUnit_isPerfectoidization
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedSideProjection
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedSideProjection_comp
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedSideProjection_eq_zero_of_mem
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedSideProjection_originalIdeal
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedComparison_ideal_le
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedComparison
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedComparison_square
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedComparison_unit
#print axioms SerrePositivity.BhattScholze.perfectoidizationClosedComparison_eq_map
#print axioms SerrePositivity.CLMST.perfectoidization_comparison_almost_of_canonical_excision

noncomputable section
universe u
open SerrePositivity SerrePositivity.BhattScholze CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

-- The actual closed quotient kills the original base ideal, not a substitute ideal.
theorem audit_closedSide_original_generator
    (R A C : Type u) [CommRing R] [CommRing A] [CommRing C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (α : R →+* A) (f : A →+* C) (hf : IsPerfectoidization p f) (a s : R)
    (hs : s ∈ perfectoidIdeal R p hR a) :
    perfectoidizationClosedSideProjection hf (Ideal.span {α a}) (f (α s)) = 0 := by
  exact perfectoidizationClosedSideProjection_originalIdeal hR α hf (Ideal.span {α a}) a
    (Ideal.subset_span (Set.mem_singleton _)) s hs

-- At the unit ideal the actual closed-side universal target is a zero ring.
theorem audit_closedSide_top_subsingleton
    (A C : Type u) [CommRing A] [CommRing C] (p : ℕ) [Fact p.Prime]
    (f : A →+* C) (hf : IsPerfectoidization p f) :
    Subsingleton (QuotientPerfectoidization C ((⊤ : Ideal A).map f) p hf.1) :=
  (perfectoidizationClosedSideUnit hf ⊤).codomain_trivial

-- Commutativity alone cannot supply the missing excision assertion.
-- The all-zero closed square over a nonzero ring is a concrete counterexample.
theorem audit_no_excision_from_commutativity
    (R : Type u) [CommRing R] [Nontrivial R] :
    let Z := Fin 0 → R
    let q : R →+* Z := RingHom.pi fun i => Fin.elim0 i
    ¬ IsPullback (CommRingCat.ofHom q) (CommRingCat.ofHom q)
      (CommRingCat.ofHom (RingHom.id Z)) (CommRingCat.ofHom (RingHom.id Z)) := by
  let Z := Fin 0 → R
  let q : R →+* Z := RingHom.pi fun i => Fin.elim0 i
  change ¬ IsPullback (CommRingCat.ofHom q) (CommRingCat.ofHom q)
    (CommRingCat.ofHom (RingHom.id Z)) (CommRingCat.ofHom (RingHom.id Z))
  intro hPB
  have hPB' := hPB.map (forget CommRingCat)
  have he : (1 : R) = 0 := Types.ext_of_isPullback hPB'
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  exact one_ne_zero he

assert_no_sorry audit_closedSide_original_generator
assert_no_sorry audit_closedSide_top_subsingleton
assert_no_sorry audit_no_excision_from_commutativity
#print axioms audit_closedSide_original_generator
#print axioms audit_closedSide_top_subsingleton
#print axioms audit_no_excision_from_commutativity
