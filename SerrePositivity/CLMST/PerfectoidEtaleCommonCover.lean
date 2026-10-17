module

public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedEtaleAwayCover
public import SerrePositivity.CommutativeAlgebra.DoubleLocalizationTensorComparison
public import SerrePositivity.CLMST.PerfectoidFinitePresentationCommonModel
public import SerrePositivity.CommutativeAlgebra.LocalizationComparisonTensorEquiv

/-! # Derived complete common models on the actual finite etale splitting cover

The finite cover, its varying ranks and its comparison models are fixed before
perfectoidizations and Tor tests. No excision or almost invariance is asserted.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The actual finite splitting cover off g has finite presentation, derived
p-complete common models with both original finite maps and supported errors.
The two tensor maps are bijective, and the rank may vary with the cover member. -/
theorem aic_finiteEtaleAway_exists_derivedComplete_common_cover
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      ∃ t : Finset (Localization.Away g),
        Ideal.span (t : Set (Localization.Away g)) = ⊤ ∧
        (∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range (fun f : t =>
          g * (IsLocalization.Away.sec g f.1).1))) ∧
        ∀ f ∈ t, ∃ (r : ℕ)
          (e : (Localization.Away f) ⊗[Localization.Away g]
            (Localization.Away (algebraMap R A g)) ≃ₐ[Localization.Away f]
              (Fin r → Localization.Away f))
          (E : Type u) (_ : CommRing E) (_ : Algebra R E),
          Module.Finite R E ∧ Algebra.FinitePresentation R E ∧ Module.FinitePresentation R E ∧
          IsModuleComplete R (p : R) (ModuleCat.of R E) ∧
          IsModuleComplete E (p : E) (ModuleCat.of E E) ∧
          IsModuleComplete E (p : E) (ModuleCat.of E
            (Ideal.span {algebraMap R E (g * (IsLocalization.Away.sec g f).1)})) ∧
          IsModuleComplete (E ⧸ Ideal.span {algebraMap R E (g * (IsLocalization.Away.sec g f).1)})
            (p : E ⧸ Ideal.span {algebraMap R E (g * (IsLocalization.Away.sec g f).1)})
            (ModuleCat.of (E ⧸ Ideal.span {algebraMap R E (g * (IsLocalization.Away.sec g f).1)})
              (E ⧸ Ideal.span {algebraMap R E (g * (IsLocalization.Away.sec g f).1)})) ∧
          ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E)
            (w : E →ₐ[R] (Fin r → Localization.Away f)),
            (∀ a, w (u a) = e ((1 : Localization.Away f) ⊗ₜ[Localization.Away g]
              algebraMap A (Localization.Away (algebraMap R A g)) a)) ∧
            (∀ b i, w (v b) i = algebraMap R (Localization.Away f) (b i)) ∧
            IsLocalizedModule (.powers (g * (IsLocalization.Away.sec g f).1)) w.toLinearMap ∧
            u.toRingHom.Finite ∧ v.toRingHom.Finite ∧
            Function.Bijective (Algebra.TensorProduct.map
              (AlgHom.id (Localization.Away f) (Localization.Away f)) u) ∧
            Function.Bijective (Algebra.TensorProduct.map
              (AlgHom.id (Localization.Away f) (Localization.Away f)) v) ∧
            (∀ a, u a = 0 → ∃ n : ℕ, (g * (IsLocalization.Away.sec g f).1) ^ n • a = 0) ∧
            (∀ b, v b = 0 → ∃ n : ℕ, (g * (IsLocalization.Away.sec g f).1) ^ n • b = 0) ∧
            ∃ n : ℕ,
              (∀ y : E ⧸ u.toLinearMap.range, (g * (IsLocalization.Away.sec g f).1) ^ n • y = 0) ∧
              (∀ y : E ⧸ v.toLinearMap.range,
                (g * (IsLocalization.Away.sec g f).1) ^ n • y = 0) := by
  let := GenericEtale.awayAlgebra R A g
  intro hetale
  obtain ⟨t, ht, hsplit, hcover⟩ := hAIC.finiteEtaleAway_exists_finite_cover g hetale
  refine ⟨t, ht, hcover, ?_⟩
  intro f hf
  obtain ⟨r, ⟨e⟩⟩ := hsplit f hf
  let d := g * (IsLocalization.Away.sec g f).1
  let : IsLocalization (.powers d) (Localization.Away f) :=
    principalLocalizationTower_isLocalization g f
  let e' := (doubleLocalizationTensorEquiv R A g f).trans e
  obtain ⟨E, hE, aE, hfinite, hfp, hmfp, hcR, hcE, hcI, hcQ,
    u, v, w, hu, hv, hloc, huF, hvF, huk, hvk, n, huc, hvc⟩ :=
    localizationSplitting_exists_derivedComplete_common_model p hR d (Localization.Away f) r e'
  let : IsLocalizedModule (.powers d) w.toLinearMap := hloc
  obtain ⟨htu, htv⟩ := localizationSplitting_common_model_tensorMaps_bijective
    (.powers d) (Localization.Away f) r e' u v w hu hv
  refine ⟨r, e, E, hE, aE, hfinite, hfp, hmfp, hcR, hcE, hcI, hcQ,
    u, v, w, ?_, hv, hloc, huF, hvF, htu, htv, huk, hvk, n, huc, hvc⟩
  intro a
  rw [hu]
  change e (doubleLocalizationTensorEquiv R A g f ((1 : Localization.Away f) ⊗ₜ[R] a)) = _
  rw [doubleLocalizationTensorEquiv_tmul]

end SerrePositivity.CLMST
