module

public import SerrePositivity.BhattScholze.Almost.PerfectoidizationImageComparison
public import SerrePositivity.CLMST.PerfectoidIdealTorTransport
public import SerrePositivity.CommutativeAlgebra.LocalizationComparisonBounds

/-! # Actual Tor comparison with the perfectoidization of a localization image

The kernel support comes from the original localization map, rather than an
assumed almost comparison. The image target is chosen before all Tor tests.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory
variable {R A E C D : Type u}
    [CommRing R] [CommRing A] [CommRing E] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R E] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C}

/-- Actual source-to-image comparison preserves all original ideal Tor tests. -/
theorem perfectoidIdeal_TorInput_iff_image
    (hR : IsIntegralPerfectoid R p) (φ : A →ₐ[R] E)
    (hf : IsPerfectoidization p f.toRingHom)
    (g : φ.range →ₐ[R] D) (hg : IsPerfectoidization p g.toRingHom)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a, φ a = 0 → ∃ e : ℕ, ρ 0 ^ e • a = 0)
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0) (i : ℕ) :
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0) := by
  obtain ⟨hker, hcoker⟩ :=
    BhattScholze.perfectoidization_image_ker_coker_annihilated hR φ hf g hg ρ hρ hk
  exact torCoefficientIdeal_eq_zero_iff_of_almost_comparison
    (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict).toLinearMap
    (perfectoidIdeal R p hR (ρ 0)) hker hcoker N ((p : R) ^ k) hN
    (perfectoidIdeal_mod_power_idempotent R p hR (ρ 0) k) i

/-- An ordinary localization comparison supplies an actual image target once,
with all Tor tests preserved; no almost kernel hypothesis is assumed. -/
theorem exists_localization_image_perfectoidization_Tor_comparison
    [Module.Finite R A] (hR : IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (φ : A →ₐ[R] E) (hf : IsPerfectoidization p f.toRingHom)
    {X : Type u} [AddCommGroup X] [Module R X]
    (α : A →ₗ[R] X) [IsLocalizedModule (.powers (ρ 0)) α]
    (j : E →ₗ[R] X) (hcomm : j.comp φ.toLinearMap = α) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (g : φ.range →ₐ[R] D),
      IsPerfectoidization p g.toRingHom ∧
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) → ∀ i : ℕ,
        (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
          torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
        (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
          torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0) := by
  have hk : ∀ a, φ a = 0 → ∃ e : ℕ, ρ 0 ^ e • a = 0 :=
    localizationComparison_ker_power_torsion (ρ 0) φ.toLinearMap α j hcomm
  obtain ⟨D, hD, hDalg, g, hg, _⟩ :=
    BhattScholze.exists_image_perfectoidization_almost_comparison hR φ hf ρ hρ hk
  let := hD
  let := hDalg
  exact ⟨D, hD, hDalg, g, hg,
    fun N k hN i => perfectoidIdeal_TorInput_iff_image hR φ hf g hg ρ hρ hk N k hN i⟩

end SerrePositivity.CLMST
