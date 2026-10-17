module

public import SerrePositivity.CLMST.CanonicalExcisionTorInput
public import SerrePositivity.CLMST.PerfectoidEtaleCommonCover
public import SerrePositivity.CLMST.PerfectoidIdealTorCover

/-! # The full AIC Tor input from the remaining finite-comparison excision input

The input below is an explicit proposition about the actual canonical ring
squares. It is not asserted here, cited, or replaced by a Tor-zero hypothesis.
The finite cover and all comparison models are constructed by proved theorems.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory CategoryTheory.Limits BhattScholze
set_option backward.isDefEq.respectTransparency false

/-- The exact canonical excision square for the specified original units. -/
abbrev KLCanonicalExcisionSquare
    {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C} {g : B →ₐ[R] D}
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (q : A →ₐ[R] B) (a : R) : Prop :=
  IsPullback
    (CommRingCat.ofHom (IsPerfectoidization.map hf hg q.toRingHom))
    (CommRingCat.ofHom (perfectoidizationClosedSideProjection hf
      (Ideal.span {algebraMap R A a})))
    (CommRingCat.ofHom (perfectoidizationClosedSideProjection hg
      ((Ideal.span {algebraMap R A a}).map q.toRingHom)))
    (CommRingCat.ofHom (perfectoidizationClosedComparison hf hg q.toRingHom
      (Ideal.span {algebraMap R A a})))

/-- Unproved excision input needed by KL, with the actual finite presentation
sources, finite map and supported errors. Completeness and localization data
for the applications have already been proved; the pullback assertion has not. -/
def KLFiniteComparisonExcision (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    [Module.Finite R A] [Module.Finite R B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B]
    (a : R) (q : A →ₐ[R] B) (_hq : q.toRingHom.Finite)
    (_hk : ∀ x, q x = 0 → ∃ n : ℕ, a ^ n • x = 0)
    (_hc : ∃ n : ℕ, ∀ y : B ⧸ q.toLinearMap.range, a ^ n • y = 0)
    (f : A →ₐ[R] C) (g : B →ₐ[R] D)
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom),
    KLCanonicalExcisionSquare hf hg q a

/-- On the AIC base, the sole missing finite-comparison excision assertion
supplies the full original ideal Tor input. Every local model and universal
unit is fixed before all power-torsion tests. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_aic_finiteComparison_excision
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (hExcision : KLFiniteComparisonExcision R p)
    (a : R) (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    letI := GenericEtale.awayAlgebra R A a
    Algebra.Etale (Localization.Away a) (Localization.Away (algebraMap R A a)) →
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
        ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR a,
          torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  let := GenericEtale.awayAlgebra R A a
  intro hetale
  obtain ⟨t, ht, _hpow, hmodels⟩ :=
    aic_finiteEtaleAway_exists_derivedComplete_common_cover p hR hAIC a hetale
  apply perfectoidIdeal_powerTorsionTorInput_of_aic_principal_cover R p hR hAIC a t ht C
  intro z
  obtain ⟨r, _e, M, hM, aM, hfinite, hfp, _hmfp, _hcR, _hcM, _hcI, _hcQ,
    u, v, _w, _hu, _hv, _hloc, huF, hvF, _htu, _htv, huk, hvk, n, huc, hvc⟩ :=
    hmodels z.1 z.2
  let : Module.Finite R M := hfinite
  let : Algebra.FinitePresentation R M := hfp
  obtain ⟨D, hD, g₀, hg₀⟩ := Inputs.exists_perfectoidization_of_integral R M p hR
  let := hD
  let : Algebra R D := (g₀.comp (algebraMap R M)).toAlgebra
  let g : M →ₐ[R] D := { g₀ with commutes' := fun _ => rfl }
  have hg : IsPerfectoidization p g.toRingHom := hg₀
  let h : (Fin r → R) →ₐ[R] (Fin r → R) := AlgHom.id R _
  have hh : IsPerfectoidization p h.toRingHom :=
    (isIntegralPerfectoid_finPi R p hR r).isPerfectoidization_id
  exact perfectoidIdeal_powerTorsionTorInput_of_two_canonical_excision p hR
    (a * (IsLocalization.Away.sec a z.1).1) r u v f g h hf hg hh
    (hExcision A M C D _ u huF huk ⟨n, huc⟩ f g hf hg)
    (hExcision (Fin r → R) M (Fin r → R) D _ v hvF hvk ⟨n, hvc⟩ h g hh hg)

end SerrePositivity.CLMST
