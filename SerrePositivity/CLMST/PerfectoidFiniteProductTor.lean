module

public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.CLMST.PerfectoidizationImageTorComparison
public import SerrePositivity.CommutativeAlgebra.FiniteCommonLocalizationBounds

/-! # Actual Tor inputs for the finite-product leg and its supported image

No almost input is assumed: the free source is identified through its original
universal unit, and the supported image comparison is the one already proved.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

/-- Any specified perfectoidization of the finite product has its original
finite-free module structure over R, and in particular is flat. -/
theorem finiteProduct_perfectoidization_flat
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : (Fin r → R) →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    Module.Flat R C := by
  obtain ⟨e, _⟩ := BhattScholze.finiteProduct_perfectoidization_exists_algEquiv R p hR r C f hf
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

/-- Every coefficient endomorphism in positive Tor is zero for the actual
perfectoidization of R^r, even for test modules with no torsion hypothesis. -/
theorem finiteProduct_perfectoidization_Tor_zero
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : (Fin r → R) →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (N : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (c : C) :
    torCoefficientScalarEndomorphism C N i c = 0 := by
  let := finiteProduct_perfectoidization_flat R p hR r C f hf
  have hz : IsZero (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj N) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torModule_subsingleton_of_flat (R := R) C N j)
  exact hz.eq_of_src _ _

/-- The supported actual image of the finite-product leg has the full original
ideal Tor input. The image target is fixed before all test modules and degrees. -/
theorem supported_finiteProduct_image_powerTorsionTorInput
    {R E D : Type u} [CommRing R] [CommRing E] [CommRing D]
    [Algebra R E] [Algebra R D] {p : ℕ} [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ) (φ : (Fin r → R) →ₐ[R] E)
    (g : φ.range →ₐ[R] D) (hg : IsPerfectoidization p g.toRingHom)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a, φ a = 0 → ∃ e : ℕ, ρ 0 ^ e • a = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR (ρ 0),
        torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0 := by
  let f : (Fin r → R) →ₐ[R] (Fin r → R) := AlgHom.id R (Fin r → R)
  have hf : IsPerfectoidization p f.toRingHom :=
    (BhattScholze.isIntegralPerfectoid_finPi R p hR r).isPerfectoidization_id
  intro N k hN i hi s hs
  have hiff := perfectoidIdeal_TorInput_iff_image hR φ hf g hg ρ hρ hk N k hN i
  exact hiff.mp (fun t _ =>
    finiteProduct_perfectoidization_Tor_zero R p hR r (Fin r → R) f hf N i hi
      (algebraMap R (Fin r → R) t)) s hs

/-- The actual finite common model of a localized splitting has a finite-product
image perfectoidization with all original positive Tor actions almost zero. -/
theorem localizationSplitting_exists_finiteProduct_image_TorInput
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    {p : ℕ} [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers (ρ 0)) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ E : Subalgebra R (Fin r → L), Module.Finite R E ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        (∀ a, E.val (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        (∀ b i, E.val (v b) i = algebraMap R L (b i)) ∧
        ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (g : v.range →ₐ[R] D),
          IsPerfectoidization p g.toRingHom ∧
          ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
            ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR (ρ 0),
              torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0 := by
  obtain ⟨E, hE, _hloc, u, v, hu, hv, _huF, _hvF, _huk, hvk, _⟩ :=
    localizationSplitting_exists_finite_common_model_bounds (ρ 0) L r e
  let f : (Fin r → R) →ₐ[R] (Fin r → R) := AlgHom.id R (Fin r → R)
  have hf : IsPerfectoidization p f.toRingHom :=
    (BhattScholze.isIntegralPerfectoid_finPi R p hR r).isPerfectoidization_id
  obtain ⟨D, hD, hDalg, g, hg, _⟩ :=
    BhattScholze.exists_image_perfectoidization_almost_comparison hR v hf ρ hρ hvk
  let := hD
  let := hDalg
  exact ⟨E, hE, u, v, hu, hv, D, hD, hDalg, g, hg,
    supported_finiteProduct_image_powerTorsionTorInput hR r v g hg ρ hρ hvk⟩

end SerrePositivity.CLMST
