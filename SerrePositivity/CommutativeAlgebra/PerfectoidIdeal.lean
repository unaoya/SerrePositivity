module

public import SerrePositivity.BhattScholze.Semiperfectoid.Perfectoidization
public import Mathlib.RingTheory.FinitePresentation

/-! # B3による主イデアル商から定義するperfectoid ideal -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity

/-- CLMSTの(g)_perfd。B3の標準写像との合成の核で定義する。 -/
def perfectoidIdeal (R : Type u) [CommRing R]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R) : Ideal R :=
  RingHom.ker ((toQuotientPerfectoidization R (Ideal.span {g}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {g})))

end SerrePositivity
