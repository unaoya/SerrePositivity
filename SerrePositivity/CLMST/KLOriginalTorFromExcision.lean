module

public import SerrePositivity.CLMST.KLAicTorFromExcision
public import SerrePositivity.CLMST.AndrePerfectoidIdealTorDescent
public import SerrePositivity.CommutativeAlgebra.EtaleAwayTensorBaseChange

/-! # The original full Tor input from excision on one actual Andre extension

The missing excision proposition remains explicit. All other choices and maps
are the actual finite cover, ordinary tensor and specified universal units.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- One Andre extension is selected before all finite presentation algebras,
generators, universal targets and tests. Excision on this same extension then
supplies the original full ideal Tor input for every algebra etale off a. -/
theorem exists_andre_extension_finiteComparison_excision_suffices
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      ∃ _hE : IsIntegralPerfectoid E p,
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∃ ρ : E → ℕ → E, (∀ s, ρ s 0 = s) ∧ (∀ s n, ρ s (n + 1) ^ p = ρ s n) ∧
      (KLFiniteComparisonExcision E p →
        ∀ (A C : Type u) [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
          [Module.Finite R A] [Algebra.FinitePresentation R A]
          (a : R) (f : A →ₐ[R] C) (_hf : IsPerfectoidization p f.toRingHom),
          letI := GenericEtale.awayAlgebra R A a
          Algebra.Etale (Localization.Away a) (Localization.Away (algebraMap R A a)) →
            ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
              ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR a,
                torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, hdesc⟩ :=
    exists_andre_extension_descends_perfectoidIdeal_powerTorsionTorInput R p hR
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, ?_⟩
  intro hExcision A C _ _ _ _ _ _ a f hf
  let := GenericEtale.awayAlgebra R A a
  intro hetale
  obtain ⟨D, hD, g₀, hg₀⟩ :=
    BhattScholze.Inputs.exists_perfectoidization_of_integral E (E ⊗[R] A) p hE
  let := hD
  let : Algebra E D := (g₀.comp (algebraMap E (E ⊗[R] A))).toAlgebra
  let g : E ⊗[R] A →ₐ[E] D := { g₀ with commutes' := fun _ => rfl }
  have hg : IsPerfectoidization p g.toRingHom := hg₀
  have he := etaleAway_tensor_baseChange (B := E) a hetale
  let := GenericEtale.awayAlgebra E (E ⊗[R] A) (algebraMap R E a)
  have hTor := perfectoidIdeal_powerTorsionTorInput_of_aic_finiteComparison_excision
    p hE haic hExcision (algebraMap R E a) g hg he
  exact hdesc A C f hf D g hg a hTor

/-- The original full Tor statement follows once the explicit finite-comparison
excision input is supplied on AIC perfectoid extensions of the original base.
This theorem remains conditional on that input. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hExcision : ∀ (E : Type u) [CommRing E] [Algebra R E],
      IsIntegralPerfectoid E p → IsAbsolutelyIntegrallyClosed E → KLFiniteComparisonExcision E p)
    (a : R) (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    letI := GenericEtale.awayAlgebra R A a
    Algebra.Etale (Localization.Away a) (Localization.Away (algebraMap R A a)) →
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
        ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR a,
          torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  let := GenericEtale.awayAlgebra R A a
  intro hetale
  obtain ⟨E, hEring, hEalg, hE, _hflat, haic, _ρ, _hρ0, _hρ, hTor⟩ :=
    exists_andre_extension_finiteComparison_excision_suffices R p hR
  exact hTor (hExcision E hE haic) A C a f hf hetale

end SerrePositivity.CLMST
