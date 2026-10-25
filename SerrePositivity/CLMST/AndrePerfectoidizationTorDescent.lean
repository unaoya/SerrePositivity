module
public import SerrePositivity.CLMST.AndreTorDescent
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationCompletedBaseChange

/-! # One actual André extension detects Tor after base-changing the original perfectoidization

The sole permitted deep input is the existing BS Theorem 7.14 extension.
Actual almost comparisons and their Tor annihilation remain separate proofs.
-/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard

/-- Choose one extension before the original algebra, its perfectoidization,
the base-changed perfectoidization model, and all power-torsion Tor tests. -/
lemma exists_andre_extension_detects_baseChangedPerfectoidizationTor
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      IsIntegralPerfectoid E p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∃ ρ : E → ℕ → E, (∀ s, ρ s 0 = s) ∧
      (∀ s n, ρ s (n + 1) ^ p = ρ s n) ∧
      ∀ (A C : Type u) [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
        (f : A →ₐ[R] C) (_hf : IsPerfectoidization p f.toRingHom)
        (D : Type u) [CommRing D] [Algebra E D] (g : E ⊗[R] A →ₐ[E] D)
        (_hg : IsPerfectoidization p g.toRingHom)
        (N : ModuleCat.{u} R) (k : ℕ) (_hN : ∀ x : N, (p : R) ^ k • x = 0)
        (i : ℕ) (s : R),
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
          ∀ x : (((Tor (ModuleCat E) i).obj (ModuleCat.of E D)).obj
            ((ModuleCat.extendScalars (algebraMap R E)).obj N)), algebraMap R E s • x = 0 := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, _hdet⟩ :=
    exists_andre_extension_detects_powerTorsion_Tor R p hR
  letI := hEring
  letI := hEalg
  have hφ : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)) :=
    isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R)})
      (algebraSelfRestrictionIso R E).toLinearEquiv.symm hflat
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, ?_⟩
  intro A C _ _ _ _ f hf D _ _ g hg N k hN i s
  exact BhattScholze.perfectoidization_torCoefficientScalar_eq_zero_iff_baseChangedPerfectoidizationTor
    R p E A C hR hE hφ f hf D g hg N k hN i s

end SerrePositivity.CLMST
