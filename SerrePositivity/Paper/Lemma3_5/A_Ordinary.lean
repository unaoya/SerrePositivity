module

public import SerrePositivity.PerfectComplex.OrdinaryEuler

/-!
# Ordinary-length part of Lemma 3.5a

The general ordinary Euler theorem applies to a finite algebra over a
Noetherian local ring and a tuple generating a primary ideal for its closed
point. The algebra need not be local, and no normalized-length data is used.
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- Extending a primary ideal for the closed point along a finite algebra
gives an Artinian quotient. -/
lemma isArtinianRing_quotient_span_of_finite (A T : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T] [Algebra A T]
    [Module.Finite A T] {e : ℕ} (z : Fin e → A)
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A) :
    IsArtinianRing (T ⧸ Ideal.span (Set.range (algebraMap A T ∘ z))) := by
  let I := Ideal.span (Set.range z)
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  have : IsArtinianRing (A ⧸ I) :=
    isArtinianRing_quotient_of_le_radical (maximalIdeal A) I (by rw [hz])
  have : Module.Finite A (T ⧸ I.map (algebraMap A T)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (I.map (algebraMap A T))).toLinearMap
      Ideal.Quotient.mk_surjective
  have : Module.Finite (A ⧸ I) (T ⧸ I.map (algebraMap A T)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hI : I.map (algebraMap A T) =
      Ideal.span (Set.range (algebraMap A T ∘ z)) := by
    dsimp only [I]
    rw [Ideal.map_span, Set.range_comp]
  rw [← hI]
  exact IsArtinianRing.of_finite (A ⧸ I) (T ⧸ I.map (algebraMap A T))

/-- **Lemma 3.5a, ordinary length**: finite-length homology and a homomorphism
on supported `K₀`. Only the ordinary algebraic assumptions are required. -/
theorem lemma_3_5a_ord (A T : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T] [Algebra A T]
    [Module.Finite A T] {e : ℕ} (z : Fin e → A)
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A) :
    (∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ), Module.length T (P.1.homology i) ≠ ⊤) ∧
      (∃ χ : K0Supported T (algebraMap A T ∘ z) →+ ℝ,
        ∀ P, χ (K0.mk P) = chiOrd P.1) := by
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := isArtinianRing_quotient_span_of_finite A T z hz
  exact ordinary_euler_of_artinian_quotient (algebraMap A T ∘ z)

end SerrePositivity
