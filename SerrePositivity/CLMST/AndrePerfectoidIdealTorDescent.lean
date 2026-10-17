module

public import SerrePositivity.CLMST.AndrePerfectoidizationTorDescent
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealFunctor
public import SerrePositivity.CLMST.PerfectoidIdealTorCover
public import SerrePositivity.HomologicalAlgebra.ModuleScalarExtensionAnnihilator

/-! # Descent of the full original perfectoid-ideal Tor input

The test module is extended by the actual scalar extension functor and retains
its exponent. A single Andre extension is chosen before the algebra, generator,
perfectoidization models and all tests. No local excision assertion is supplied here.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.CLMST
open CategoryTheory BhattScholze
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard

/-- Full ideal Tor annihilation over a specified completely faithfully flat
perfectoid extension descends to the original perfectoidization and ideal. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_baseChangedPerfectoidization
    (R E A C : Type u) [CommRing R] [CommRing E] [CommRing A] [CommRing C]
    [Algebra R E] [Algebra R A] [Algebra R C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hE : IsIntegralPerfectoid E p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)))
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (D : Type u) [CommRing D] [Algebra E D]
    (g : E ⊗[R] A →ₐ[E] D) (hg : IsPerfectoidization p g.toRingHom) (a : R)
    (hTor : ∀ (L : ModuleCat.{u} E) (k : ℕ), (∀ x : L, (p : E) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal E p hE (algebraMap R E a),
        torCoefficientScalarEndomorphism D L i (algebraMap E D s) = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR a,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  intro N k hN i hi s hs
  let L := (ModuleCat.extendScalars (algebraMap R E)).obj N
  have hL : ∀ x : L, (p : E) ^ k • x = 0 := by
    simpa only [map_pow, map_natCast] using
      scalarExtension_annihilated (algebraMap R E) ((p : R) ^ k) N hN
  have hsE := map_mem_perfectoidIdeal p hR hE (algebraMap R E) a s hs
  have hz := hTor L k hL i hi (algebraMap R E s) hsE
  rw [torCoefficientScalar_algebraMap_eq_smul_id] at hz
  apply (perfectoidization_torCoefficientScalar_eq_zero_iff_baseChangedPerfectoidizationTor
    R p E A C hR hE hflat f hf D g hg N k hN i s).mpr
  intro x
  exact congrArg (fun m => m.hom x) hz

/-- The finite principal cover input on an AIC extension supplies all original
ideal Tor tests. The cover and coefficient models precede the test module. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_baseChanged_aic_principal_cover
    (R E A C : Type u) [CommRing R] [CommRing E] [CommRing A] [CommRing C]
    [Algebra R E] [Algebra R A] [Algebra R C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hE : IsIntegralPerfectoid E p)
    (hAIC : IsAbsolutelyIntegrallyClosed E)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)))
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (D : Type u) [CommRing D] [Algebra E D]
    (g : E ⊗[R] A →ₐ[E] D) (hg : IsPerfectoidization p g.toRingHom) (a : R)
    (t : Finset (Localization.Away (algebraMap R E a)))
    (ht : Ideal.span (t : Set (Localization.Away (algebraMap R E a))) = ⊤)
    (hlocal : ∀ q : t, ∀ (L : ModuleCat.{u} E) (k : ℕ),
      (∀ x : L, (p : E) ^ k • x = 0) → ∀ i : ℕ, 0 < i →
      ∀ s ∈ perfectoidIdeal E p hE
        (algebraMap R E a * (IsLocalization.Away.sec (algebraMap R E a) q.1).1),
        torCoefficientScalarEndomorphism D L i (algebraMap E D s) = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR a,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  apply perfectoidIdeal_powerTorsionTorInput_of_baseChangedPerfectoidization
    R E A C p hR hE hflat f hf D g hg a
  exact perfectoidIdeal_powerTorsionTorInput_of_aic_principal_cover E p hE hAIC
    (algebraMap R E a) t ht D hlocal

/-- One actual Andre extension suffices for all algebras, generators, specified
perfectoidizations and all original ideal Tor tests; none is chosen per test. -/
theorem exists_andre_extension_descends_perfectoidIdeal_powerTorsionTorInput
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      ∃ hE : IsIntegralPerfectoid E p,
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∃ ρ : E → ℕ → E, (∀ s, ρ s 0 = s) ∧ (∀ s n, ρ s (n + 1) ^ p = ρ s n) ∧
      ∀ (A C : Type u) [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
        (f : A →ₐ[R] C) (_hf : IsPerfectoidization p f.toRingHom)
        (D : Type u) [CommRing D] [Algebra E D] (g : E ⊗[R] A →ₐ[E] D)
        (_hg : IsPerfectoidization p g.toRingHom) (a : R),
        (∀ (L : ModuleCat.{u} E) (k : ℕ), (∀ x : L, (p : E) ^ k • x = 0) →
          ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal E p hE (algebraMap R E a),
            torCoefficientScalarEndomorphism D L i (algebraMap E D s) = 0) →
        ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
          ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR a,
            torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, _hdet⟩ :=
    exists_andre_extension_detects_baseChangedPerfectoidizationTor R p hR
  have hflat' : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)) :=
    isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R)})
      (algebraSelfRestrictionIso R E).toLinearEquiv.symm hflat
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, ?_⟩
  intro A C _ _ _ _ f hf D _ _ g hg a hTor
  exact perfectoidIdeal_powerTorsionTorInput_of_baseChangedPerfectoidization
    R E A C p hR hE hflat' f hf D g hg a hTor

end SerrePositivity.CLMST
