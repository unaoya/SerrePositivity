module
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedEtaleCover
public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import SerrePositivity.CommutativeAlgebra.PrincipalCoverNumerators

/-! # Actual finite splitting covers off the original bad principal ideal -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct

/-- Finite étaleness away from the original g supplies an actual finite splitting
cover there. Its original scaled numerators cover D(g), witnessed by one power of g. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtaleAway_exists_finite_cover
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (hR : IsAbsolutelyIntegrallyClosed R) (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      ∃ t : Finset (Localization.Away g),
        Ideal.span (t : Set (Localization.Away g)) = ⊤ ∧
        (∀ f ∈ t, ∃ r : ℕ,
          Nonempty ((Localization.Away f) ⊗[Localization.Away g]
            (Localization.Away (algebraMap R A g)) ≃ₐ[Localization.Away f]
              (Fin r → Localization.Away f))) ∧
        ∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range (fun f : t =>
          g * (IsLocalization.Away.sec g f.1).1)) := by
  letI := GenericEtale.awayAlgebra R A g
  intro hetale
  letI := hetale
  letI : Module.Finite (Localization.Away g) (Localization.Away (algebraMap R A g)) :=
    GenericEtale.finite_away R A g
  obtain ⟨t, ht, hsplit⟩ := (hR.localization (Submonoid.powers g) (Localization.Away g)).finiteEtale_exists_finite_principal_cover
    (A := Localization.Away (algebraMap R A g))
  exact ⟨t, ht, hsplit, exists_pow_mem_span_scaled_cover_numerators g t ht⟩

end SerrePositivity
