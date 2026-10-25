module

public import SerrePositivity.BhattScholze.Results.PerfectoidizationSupportedQuotientLinear
public import SerrePositivity.BhattScholze.Inputs.Perfectoidization
public import Mathlib.RingTheory.Finiteness.Basic

/-! # The actual supported quotient onto the image of a finite comparison

This constructs the surjective part of a modification comparison. It does not
assume or assert almost invariance of the remaining injective inclusion.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R A E C D : Type u}
    [CommRing R] [CommRing A] [CommRing E] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R E] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C}

/-- The original comparison to its actual image gives a supported surjection,
so its universal perfectoidizations have almost-zero kernel and cokernel. -/
theorem perfectoidization_image_ker_coker_annihilated
    (hR : IsIntegralPerfectoid R p) (φ : A →ₐ[R] E)
    (hf : IsPerfectoidization p f.toRingHom)
    (g : φ.range →ₐ[R] D) (hg : IsPerfectoidization p g.toRingHom)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a, φ a = 0 → ∃ N : ℕ, ρ 0 ^ N • a = 0) :
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      ∀ x : (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict).toLinearMap.ker, s • x = 0) ∧
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      ∀ y : D ⧸ (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict).toLinearMap.range,
        s • y = 0) := by
  apply perfectoidization_mapAlgHom_ker_coker_annihilated_of_surjective_supported_kernel
    hR hf hg φ.rangeRestrict φ.rangeRestrict_surjective ρ hρ
  intro a ha
  have hφ : φ a = 0 := congrArg (fun x : φ.range => (x : E)) ha
  obtain ⟨N, hN⟩ := hk a hφ
  refine ⟨N, ?_⟩
  simpa only [Algebra.smul_def, map_pow] using hN

/-- Choose the image perfectoidization once, before every test object. The
existence input is the existing integral-perfectoidization citation B-I. -/
theorem exists_image_perfectoidization_almost_comparison
    [Module.Finite R A] (hR : IsIntegralPerfectoid R p) (φ : A →ₐ[R] E)
    (hf : IsPerfectoidization p f.toRingHom)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a, φ a = 0 → ∃ N : ℕ, ρ 0 ^ N • a = 0) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (g : φ.range →ₐ[R] D),
      ∃ hg : IsPerfectoidization p g.toRingHom,
        (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
          ∀ x : (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict).toLinearMap.ker,
            s • x = 0) ∧
        (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
          ∀ y : D ⧸ (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict).toLinearMap.range,
            s • y = 0) := by
  let : Module.Finite R φ.range := Module.Finite.of_surjective
    φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  obtain ⟨D, hD, g, hg⟩ := Inputs.exists_perfectoidization_of_integral R φ.range p hR
  let := hD
  let : Algebra R D := (g.comp (algebraMap R φ.range)).toAlgebra
  let g' : φ.range →ₐ[R] D := { g with commutes' := fun _ => rfl }
  exact ⟨D, hD, inferInstance, g', hg,
    perfectoidization_image_ker_coker_annihilated hR φ hf g' hg ρ hρ hk⟩

/-- The actual image comparison factors the actual original comparison, over R. -/
theorem perfectoidization_image_factorization
    (φ : A →ₐ[R] E) (hf : IsPerfectoidization p f.toRingHom)
    (g : φ.range →ₐ[R] D) (hg : IsPerfectoidization p g.toRingHom)
    {F : Type u} [CommRing F] [Algebra R F]
    (h : E →ₐ[R] F) (hh : IsPerfectoidization p h.toRingHom) :
    (IsPerfectoidization.mapAlgHom hg hh φ.range.val).comp
      (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict) =
        IsPerfectoidization.mapAlgHom hf hh φ := by
  rw [IsPerfectoidization.mapAlgHom_mapAlgHom, AlgHom.val_comp_rangeRestrict]

end SerrePositivity.BhattScholze
