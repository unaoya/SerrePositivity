import SerrePositivity.CLMST.PerfectoidEtaleCommonCover
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CLMST.aic_finiteEtaleAway_exists_derivedComplete_common_cover
#print axioms SerrePositivity.CLMST.aic_finiteEtaleAway_exists_derivedComplete_common_cover

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST SerrePositivity.DerivedCompletion

-- On the actual finite cover, the two original principal ideals map to the
-- same derived complete closed ideal of the same chosen common model.
theorem audit_actual_etale_cover_closed_ideals
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      ∃ t : Finset (Localization.Away g),
        Ideal.span (t : Set (Localization.Away g)) = ⊤ ∧
        (∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range (fun f : t =>
          g * (IsLocalization.Away.sec g f.1).1))) ∧
        ∀ f ∈ t, ∃ (r : ℕ) (E : Type u) (_ : CommRing E) (_ : Algebra R E),
          Module.FinitePresentation R E ∧
          ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
            let d := g * (IsLocalization.Away.sec g f).1
            (Ideal.span {algebraMap R A d}).map u.toRingHom = Ideal.span {algebraMap R E d} ∧
            (Ideal.span {algebraMap R (Fin r → R) d}).map v.toRingHom =
              Ideal.span {algebraMap R E d} ∧
            IsModuleComplete E (p : E) (ModuleCat.of E (Ideal.span {algebraMap R E d})) := by
  let := GenericEtale.awayAlgebra R A g
  intro hetale
  obtain ⟨t, ht, hcover, hmodels⟩ :=
    aic_finiteEtaleAway_exists_derivedComplete_common_cover p hR hAIC g hetale
  refine ⟨t, ht, hcover, ?_⟩
  intro f hf
  obtain ⟨r, _e, E, hE, aE, _hfinite, _hfp, hmfp, _hcR, _hcE, hcI, _hcQ,
    u, v, _w, _⟩ := hmodels f hf
  refine ⟨r, E, hE, aE, hmfp, u, v, ?_, ?_, hcI⟩
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {u (algebraMap R A _)} = _
    rw [u.commutes]
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {v (algebraMap R (Fin r → R) _)} = _
    rw [v.commutes]

assert_no_sorry audit_actual_etale_cover_closed_ideals
#print axioms audit_actual_etale_cover_closed_ideals
