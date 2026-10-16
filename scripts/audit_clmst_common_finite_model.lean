import SerrePositivity.CommutativeAlgebra.FiniteCommonLocalizationModel
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.exists_finite_common_localization_model
assert_no_sorry SerrePositivity.principalSplitting_exists_finite_common_model
#print axioms SerrePositivity.exists_finite_common_localization_model
#print axioms SerrePositivity.principalSplitting_exists_finite_common_model

noncomputable section
universe u
open SerrePositivity
open scoped TensorProduct

-- Actual principal splittings yield integral maps preserving all original R scalars.
theorem audit_principal_common_model_integral_and_scalars
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (g : R) (r : ℕ)
    (e : (Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
      (Fin r → Localization.Away g)) :
    ∃ E : Subalgebra R (Fin r → Localization.Away g), Module.Finite R E ∧
      IsLocalizedModule (.powers g) E.val.toLinearMap ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        u.toRingHom.IsIntegral ∧ v.toRingHom.IsIntegral ∧
        (∀ x : R, E.val (u (algebraMap R A x)) =
          algebraMap R (Fin r → Localization.Away g) x) ∧
        (∀ x : R, E.val (v (algebraMap R (Fin r → R) x)) =
          algebraMap R (Fin r → Localization.Away g) x) := by
  obtain ⟨E, hfinite, hloc, u, v, _hu, _hv, huF, hvF⟩ :=
    principalSplitting_exists_finite_common_model g r e
  refine ⟨E, hfinite, hloc, u, v, huF.to_isIntegral, hvF.to_isIntegral, ?_, ?_⟩
  · intro x
    rw [u.commutes, E.val.commutes]
  · intro x
    rw [v.commutes, E.val.commutes]

-- A zero-rank splitting gives a zero common model, even when the original algebra has torsion.
theorem audit_principal_common_model_zero_rank
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (g : R)
    (e : (Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
      (Fin 0 → Localization.Away g)) :
    ∃ E : Subalgebra R (Fin 0 → Localization.Away g), Module.Finite R E ∧
      Subsingleton E ∧ IsLocalizedModule (.powers g) E.val.toLinearMap := by
  obtain ⟨E, hfinite, hloc, _⟩ := principalSplitting_exists_finite_common_model g 0 e
  exact ⟨E, hfinite, inferInstance, hloc⟩

assert_no_sorry audit_principal_common_model_integral_and_scalars
assert_no_sorry audit_principal_common_model_zero_rank
#print axioms audit_principal_common_model_integral_and_scalars
#print axioms audit_principal_common_model_zero_rank
