module

public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealCover
public import SerrePositivity.CommutativeAlgebra.Localization.PowerTorsion
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
public import SerrePositivity.HomologicalAlgebra.Koszul.ParameterAnnihilators

/-! # Gluing the original Tor annihilation input across a principal cover

The coefficient algebra and its original scalar action are fixed throughout.
All exponents, test modules and positive Tor degrees remain quantified.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- Almost-zero coefficient endomorphisms glue along any rooted cover. -/
theorem perfectoidIdeal_torCoefficientScalar_eq_zero_of_rooted_cover
    {σ : Type u} (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (g : R) (e : ℕ) (hcover : g ^ e ∈ BhattScholze.compatibleRootFamilyZeroIdeal ρ)
    (C : Type u) [CommRing C] [Algebra R C]
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0) (i : ℕ)
    (hlocal : ∀ s, ∀ a ∈ perfectoidIdeal R p hR (ρ s 0),
      torCoefficientScalarEndomorphism C N i (algebraMap R C a) = 0) :
    ∀ a ∈ perfectoidIdeal R p hR g,
      torCoefficientScalarEndomorphism C N i (algebraMap R C a) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  let J := (coefficientFunctorAnnihilator (C := C) F).comap (algebraMap R C)
  have hsum : (⨆ s, perfectoidIdeal R p hR (ρ s 0)) ≤ J := iSup_le hlocal
  have hp : Ideal.span {(p : R) ^ k} ≤ J := (Ideal.span_singleton_le_iff_mem J).mpr
    (torCoefficientScalar_algebraMap_eq_zero_of_annihilates N i ((p : R) ^ k) hN)
  exact (perfectoidIdeal_le_iSup_sup_p_pow_of_rooted_cover R p hR ρ hρ g e hcover k).trans
    (sup_le hsum hp)

/-- On an AIC base the local generators themselves suffice; compatible roots
are selected once, independently of every test module, precision and degree. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_aic_cover
    (hAIC : IsAbsolutelyIntegrallyClosed R)
    {σ : Type u} (d : σ → R) (g : R)
    (hcover : ∃ e : ℕ, g ^ e ∈ Ideal.span (Set.range d))
    (C : Type u) [CommRing C] [Algebra R C]
    (hlocal : ∀ s, ∀ (N : ModuleCat.{u} R) (k : ℕ),
      (∀ x : N, (p : R) ^ k • x = 0) → ∀ i : ℕ, 0 < i →
      ∀ a ∈ perfectoidIdeal R p hR (d s),
        torCoefficientScalarEndomorphism C N i (algebraMap R C a) = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ a ∈ perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N i (algebraMap R C a) = 0 := by
  choose ρ hρ0 hρ using fun s =>
    hAIC.exists_compatible_pow_roots (Fact.out : p.Prime).pos (d s)
  obtain ⟨e, he⟩ := hcover
  have hzero : BhattScholze.compatibleRootFamilyZeroIdeal ρ = Ideal.span (Set.range d) := by
    change Ideal.span (Set.range (fun s => ρ s 0)) = Ideal.span (Set.range d)
    rw [show (fun s => ρ s 0) = d from funext hρ0]
  rw [← hzero] at he
  intro N k hN i hi
  apply perfectoidIdeal_torCoefficientScalar_eq_zero_of_rooted_cover R p hR ρ hρ g e he C N k hN i
  intro s a ha
  rw [hρ0] at ha
  exact hlocal s N k hN i hi a ha

/-- The actual numerators of a principal cover of R[1/g] give the original full
Tor input on the AIC base, with no rank or finite-generation assumption on C. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_aic_principal_cover
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (t : Finset (Localization.Away g)) (ht : Ideal.span (t : Set (Localization.Away g)) = ⊤)
    (C : Type u) [CommRing C] [Algebra R C]
    (hlocal : ∀ f : t, ∀ (N : ModuleCat.{u} R) (k : ℕ),
      (∀ x : N, (p : R) ^ k • x = 0) → ∀ i : ℕ, 0 < i →
      ∀ a ∈ perfectoidIdeal R p hR (g * (IsLocalization.Away.sec g f.1).1),
        torCoefficientScalarEndomorphism C N i (algebraMap R C a) = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ a ∈ perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N i (algebraMap R C a) = 0 :=
  perfectoidIdeal_powerTorsionTorInput_of_aic_cover R p hR hAIC
    (fun f : t => g * (IsLocalization.Away.sec g f.1).1) g
    (exists_pow_mem_span_scaled_cover_numerators g t ht) C hlocal

end SerrePositivity.CLMST
