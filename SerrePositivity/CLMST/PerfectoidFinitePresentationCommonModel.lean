module

public import SerrePositivity.CommutativeAlgebra.FinitePresentationCommonLocalizationBounds
public import SerrePositivity.CommutativeAlgebra.PerfectoidDerivedComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalIdeal
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FinitePresentationComplete

/-! # Derived complete common models for the actual KL comparisons

The model is chosen before any perfectoidization or Tor test. Both its original
R-action and its intrinsic ring action are retained. These completeness results
do not assert the excision square required from Corollary 8.12.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- A localized splitting over a perfectoid ring has a finite presentation common
model whose ring, principal closed ideal and closed quotient are derived p-complete.
Both actual finite maps retain their supported kernels and common cokernel bound. -/
theorem localizationSplitting_exists_derivedComplete_common_model
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Module.Finite R E ∧ Algebra.FinitePresentation R E ∧ Module.FinitePresentation R E ∧
      IsModuleComplete R (p : R) (ModuleCat.of R E) ∧
      IsModuleComplete E (p : E) (ModuleCat.of E E) ∧
      IsModuleComplete E (p : E) (ModuleCat.of E (Ideal.span {algebraMap R E d})) ∧
      IsModuleComplete (E ⧸ Ideal.span {algebraMap R E d})
        (p : E ⧸ Ideal.span {algebraMap R E d})
        (ModuleCat.of (E ⧸ Ideal.span {algebraMap R E d})
          (E ⧸ Ideal.span {algebraMap R E d})) ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E) (w : E →ₐ[R] (Fin r → L)),
        (∀ a, w (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        (∀ b i, w (v b) i = algebraMap R L (b i)) ∧
        IsLocalizedModule (.powers d) w.toLinearMap ∧
        u.toRingHom.Finite ∧ v.toRingHom.Finite ∧
        (∀ a, u a = 0 → ∃ n : ℕ, d ^ n • a = 0) ∧
        (∀ b, v b = 0 → ∃ n : ℕ, d ^ n • b = 0) ∧
        ∃ n : ℕ, (∀ y : E ⧸ u.toLinearMap.range, d ^ n • y = 0) ∧
          (∀ y : E ⧸ v.toLinearMap.range, d ^ n • y = 0) := by
  obtain ⟨E, hE, aE, hfinite, hfp, hmfp, maps⟩ :=
    localizationSplitting_exists_finitePresentation_common_model_bounds d L r e
  let : Module.FinitePresentation R E := hmfp
  have hcomplete := isModuleComplete_finitePresentation_algebra_principal R E
    (p : R) (algebraMap R E d) (hR.isModuleComplete R p)
  simp only [map_natCast] at hcomplete
  exact ⟨E, hE, aE, hfinite, hfp, hmfp, hcomplete.1, hcomplete.2.1,
    hcomplete.2.2.1, hcomplete.2.2.2, maps⟩

end SerrePositivity.CLMST
