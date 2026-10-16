module
public import SerrePositivity.CLMST.PerfectoidIdealCompletedMul
public import SerrePositivity.HomologicalAlgebra.TorAlmostComparisonTransport

/-! # Actual ideal Tor inputs are invariant under either direction of almost comparison -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (C D : Type u) [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]

/-- The full original power-torsion Tor input is invariant under an actual almost
comparison. All test modules, exponents, positive degrees, and original scalars are retained. -/
theorem perfectoidIdeal_powerTorsionTorInput_iff_of_almost_comparison
    (f : C →ₗ[R] D)
    (hk : ∀ a ∈ perfectoidIdeal R p hR g, ∀ x : f.ker, a • x = 0)
    (hc : ∀ b ∈ perfectoidIdeal R p hR g, ∀ y : D ⧸ f.range, b • y = 0) :
    (∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
    (∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0) := by
  constructor
  · intro h N k hN i hi
    exact (torCoefficientIdeal_eq_zero_iff_of_almost_comparison f
      (perfectoidIdeal R p hR g) hk hc N ((p : R) ^ k) hN
      (perfectoidIdeal_mod_power_idempotent R p hR g k) i).mp (h N k hN i hi)
  · intro h N k hN i hi
    exact (torCoefficientIdeal_eq_zero_iff_of_almost_comparison f
      (perfectoidIdeal R p hR g) hk hc N ((p : R) ^ k) hN
      (perfectoidIdeal_mod_power_idempotent R p hR g k) i).mpr (h N k hN i hi)

/-- A reverse finite free almost comparison supplies the original full Tor input,
without assuming an almost inverse is represented by one fixed module map. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_reverse_finiteFree_comparison
    (r : ℕ) (f : (Fin r → R) →ₗ[R] C)
    (hk : ∀ a ∈ perfectoidIdeal R p hR g, ∀ x : f.ker, a • x = 0)
    (hc : ∀ b ∈ perfectoidIdeal R p hR g, ∀ y : C ⧸ f.range, b • y = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  intro N k hN i hi s hs
  exact torCoefficientScalar_eq_zero_of_reverse_finiteFree_almost_comparison r f
    (perfectoidIdeal R p hR g) hk hc N ((p : R) ^ k) hN
    (perfectoidIdeal_mod_power_idempotent R p hR g k) i hi s hs

end SerrePositivity.CLMST
