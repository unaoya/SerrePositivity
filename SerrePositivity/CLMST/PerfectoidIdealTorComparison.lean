module
public import SerrePositivity.BhattScholze.PerfectoidIdeal.CompletedQuotient
public import SerrePositivity.HomologicalAlgebra.Koszul.ParameterAnnihilators

/-! # The original p-power-torsion Tor input from an actual finite free almost comparison -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/-- A finite free comparison almost isomorphism supplies all original power-torsion Tor tests.
The comparison is explicit; its existence and descent from an extension are separate inputs. -/
lemma perfectoidIdeal_powerTorsionTorInput_of_finiteFree_comparison
    (C : Type u) [CommRing C] [Algebra R C]
    (r : ℕ) (f : C →ₗ[R] (Fin r → R))
    (hc : ∀ a ∈ perfectoidIdeal R p hR g, ∀ y : (Fin r → R) ⧸ f.range, a • y = 0)
    (hk : ∀ b ∈ perfectoidIdeal R p hR g, ∀ x : f.ker, b • x = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  intro N k hN i hi s hs
  exact torCoefficientScalar_eq_zero_of_finiteFree_almost_comparison r f
    (perfectoidIdeal R p hR g) hc hk N ((p : R) ^ k) hN
    (BhattScholze.perfectoidIdealMod_idempotent R p hR g k) i hi s hs

end SerrePositivity.CLMST
