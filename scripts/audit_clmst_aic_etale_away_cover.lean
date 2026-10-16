import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedEtaleAwayCover
import SerrePositivity.HomologicalAlgebra.DerivedHomologyLinear
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.exists_pow_mem_span_scaled_cover_numerators
assert_no_sorry SerrePositivity.exists_uniform_family_pow_smul_zero_of_cover
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtaleAway_exists_finite_cover
#print axioms SerrePositivity.exists_pow_mem_span_scaled_cover_numerators
#print axioms SerrePositivity.exists_uniform_family_pow_smul_zero_of_cover
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtaleAway_exists_finite_cover

noncomputable section
universe u
open SerrePositivity CategoryTheory
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

-- The scaled numerators cover precisely the original D(g), including nonreduced bases.
theorem audit_actual_etale_away_cover_support
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (hR : IsAbsolutelyIntegrallyClosed R) (g : R) (P : Ideal R) [P.IsPrime] (hgP : g ∉ P) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      ∃ t : Finset (Localization.Away g), Ideal.span (t : Set (Localization.Away g)) = ⊤ ∧
        ∃ f : t, g * (IsLocalization.Away.sec g f.1).1 ∉ P := by
  letI := GenericEtale.awayAlgebra R A g
  intro hetale
  obtain ⟨t, ht, _hsplit, N, hN⟩ := hR.finiteEtaleAway_exists_finite_cover g hetale
  refine ⟨t, ht, ?_⟩
  by_contra hnone
  push_neg at hnone
  apply hgP
  apply ‹P.IsPrime›.mem_of_pow_mem N
  have hle : Ideal.span (Set.range (fun f : t =>
      g * (IsLocalization.Away.sec g f.1).1)) ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact hnone f
  exact hle hN

-- Local exponents are uniform in all levels before gluing, and remain so afterward.
theorem audit_three_degree_tower_uniform_cover_bound
    (R : Type u) [CommRing R] (K : ℕ → DerivedCategory (ModuleCat.{u} R))
    (g : R) (t : Finset R) (hcover : ∃ k : ℕ, g ^ k ∈ Ideal.span (t : Set R))
    (hzero : ∀ a ∈ t, ∃ N : ℕ, ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj (K n), a ^ N • x = 0) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj (K n), g ^ N • x = 0 := by
  let X (j : ℕ × {i : ℤ // i ∈ Set.Icc (-2 : ℤ) 0}) : Type u :=
    (DerivedCategory.homologyFunctor (ModuleCat R) j.2.1).obj (K j.1)
  have hlocal : ∀ a ∈ t, ∃ N : ℕ, ∀ j, ∀ x : X j, a ^ N • x = 0 := by
    intro a ha
    obtain ⟨N, hN⟩ := hzero a ha
    exact ⟨N, fun j => hN j.1 j.2.1 j.2.2⟩
  obtain ⟨N, hN⟩ := exists_uniform_family_pow_smul_zero_of_cover X g t hcover hlocal
  exact ⟨N, fun n i hi => hN (n, ⟨i, hi⟩)⟩

assert_no_sorry audit_actual_etale_away_cover_support
assert_no_sorry audit_three_degree_tower_uniform_cover_bound
#print axioms audit_actual_etale_away_cover_support
#print axioms audit_three_degree_tower_uniform_cover_bound
