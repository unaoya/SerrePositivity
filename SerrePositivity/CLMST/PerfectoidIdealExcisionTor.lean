module

public import SerrePositivity.BhattScholze.PerfectoidIdeal.Cover
public import SerrePositivity.CLMST.PerfectoidIdealTorTransport

/-! # Tor transport from an actual excision square

The remaining mathematical input is the specified categorical ring pullback,
not an assumed almost comparison or an assumed Tor-zero assertion.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory CategoryTheory.Limits

/-- Actual excision transports original ideal Tor tests in every degree, for
arbitrary p-power-torsion test modules. -/
theorem perfectoidIdeal_TorInput_iff_of_isPullback
    {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : A →ₐ[R] B) (l : A →ₐ[R] C) (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hPB : IsPullback (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom l.toRingHom)
      (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (hC : IsIntegralPerfectoid C p) (g : R) (hg : algebraMap R C g = 0)
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0) (i : ℕ) :
    (∀ s ∈ perfectoidIdeal R p hR g,
      torCoefficientScalarEndomorphism A N i (algebraMap R A s) = 0) ↔
    (∀ s ∈ perfectoidIdeal R p hR g,
      torCoefficientScalarEndomorphism B N i (algebraMap R B s) = 0) := by
  obtain ⟨hk, hc⟩ := perfectoidIdeal_ker_coker_annihilated_of_isPullback
    hR f l r b hPB hC g hg
  exact torCoefficientIdeal_eq_zero_iff_of_almost_comparison f.toLinearMap
    (perfectoidIdeal R p hR g) hk hc N ((p : R) ^ k) hN
    (perfectoidIdeal_mod_power_idempotent R p hR g k) i

end SerrePositivity.CLMST
