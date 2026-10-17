module

public import SerrePositivity.CLMST.PerfectoidizationExcisionComparison
public import SerrePositivity.CLMST.PerfectoidFiniteProductTor
public import SerrePositivity.CLMST.PerfectoidIdealTorTransport

/-! # Full local Tor input from the two specified canonical excision squares

All units and comparison maps are fixed before the test module, exponent,
degree and ideal element. The two pullback assertions remain explicit inputs;
this theorem neither supplies Corollary 8.12 nor identifies derived models.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory CategoryTheory.Limits BhattScholze

/-- The two actual canonical excision squares transfer all original ideal Tor
tests from the finite free source through E to A. No almost comparison or
Tor-zero hypothesis is supplied by the caller. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_two_canonical_excision
    {R A E C D F : Type u} [CommRing R] [CommRing A] [CommRing E]
    [CommRing C] [CommRing D] [CommRing F]
    [Algebra R A] [Algebra R E] [Algebra R C] [Algebra R D] [Algebra R F]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (a : R) (r : ℕ)
    (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E)
    (f : A →ₐ[R] C) (g : E →ₐ[R] D) (h : (Fin r → R) →ₐ[R] F)
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (hh : IsPerfectoidization p h.toRingHom)
    (hPBu : IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hf hg u.toRingHom))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hf
        (Ideal.span {algebraMap R A a})))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hg
        ((Ideal.span {algebraMap R A a}).map u.toRingHom)))
      (CommRingCat.ofHom (perfectoidizationClosedComparison hf hg u.toRingHom
        (Ideal.span {algebraMap R A a}))))
    (hPBv : IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hh hg v.toRingHom))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hh
        (Ideal.span {algebraMap R (Fin r → R) a})))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hg
        ((Ideal.span {algebraMap R (Fin r → R) a}).map v.toRingHom)))
      (CommRingCat.ofHom (perfectoidizationClosedComparison hh hg v.toRingHom
        (Ideal.span {algebraMap R (Fin r → R) a})))) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR a,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  obtain ⟨huk, huc⟩ :=
    perfectoidization_comparison_almost_of_canonical_excision hR hf hg u a hPBu
  obtain ⟨hvk, hvc⟩ :=
    perfectoidization_comparison_almost_of_canonical_excision hR hh hg v a hPBv
  have hfree : ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR a,
        torCoefficientScalarEndomorphism F N i (algebraMap R F s) = 0 := by
    intro N _ _ i hi s _
    exact finiteProduct_perfectoidization_Tor_zero R p hR r F h hh N i hi
      (algebraMap R F s)
  have hD := (perfectoidIdeal_powerTorsionTorInput_iff_of_almost_comparison R p hR a F D
    (IsPerfectoidization.mapAlgHom hh hg v).toLinearMap hvk hvc).mp hfree
  exact (perfectoidIdeal_powerTorsionTorInput_iff_of_almost_comparison R p hR a C D
    (IsPerfectoidization.mapAlgHom hf hg u).toLinearMap huk huc).mpr hD

end SerrePositivity.CLMST
