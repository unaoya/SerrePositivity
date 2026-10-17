import SerrePositivity.CommutativeAlgebra.FinitePresentationCommonLocalizationBounds
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.isLocalizedModule_of_comparison_power_torsion_coker
assert_no_sorry SerrePositivity.exists_finitePresentation_common_localization_model
assert_no_sorry SerrePositivity.localizationSplitting_exists_finitePresentation_common_model_bounds
#print axioms SerrePositivity.isLocalizedModule_of_comparison_power_torsion_coker
#print axioms SerrePositivity.exists_finitePresentation_common_localization_model
#print axioms SerrePositivity.localizationSplitting_exists_finitePresentation_common_model_bounds

noncomputable section
universe u
open SerrePositivity
open scoped TensorProduct

-- At rank zero the finitely presented model need not be an embedded zero ring.
-- The actual localization map instead supplies one exponent killing the whole model.
theorem audit_zero_rank_fp_common_model
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (e : L ⊗[R] A ≃ₐ[L] (Fin 0 → L)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Module.Finite R E ∧ Module.FinitePresentation R E ∧
      ∃ (_u : A →ₐ[R] E) (_v : (Fin 0 → R) →ₐ[R] E),
        ∃ n : ℕ, ∀ z : E, d ^ n • z = 0 := by
  obtain ⟨E, hE, aE, hfinite, _hfp, hmfp, u, v, w, _hu, _hv, hloc, _⟩ :=
    localizationSplitting_exists_finitePresentation_common_model_bounds d L 0 e
  let : Module.Finite R E := hfinite
  let : IsLocalizedModule (.powers d) w.toLinearMap := hloc
  obtain ⟨n, hn⟩ := exists_uniform_power_smul_eq_zero_of_finite d (fun z : E =>
    localizationComparison_ker_power_torsion d w.toLinearMap w.toLinearMap
      LinearMap.id (by rfl) z (Subsingleton.elim _ _))
  exact ⟨E, hE, aE, hfinite, hmfp, u, v, n, hn⟩

assert_no_sorry audit_zero_rank_fp_common_model
#print axioms audit_zero_rank_fp_common_model
