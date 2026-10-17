import SerrePositivity.CommutativeAlgebra.LocalizationComparisonTensorEquiv
import SerrePositivity.CLMST.PerfectoidFinitePresentationCommonModel
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.localizationComparisonTensorEquiv
assert_no_sorry SerrePositivity.localizationComparisonTensorEquiv_tmul
assert_no_sorry SerrePositivity.localizationComparisonTensorEquiv_comp_tensorMap
assert_no_sorry SerrePositivity.localizationComparison_tensorMap_bijective
assert_no_sorry SerrePositivity.localizationSplitting_common_model_tensorMaps_bijective
assert_no_sorry SerrePositivity.localizationSplitting_common_model_tensor_squares
assert_no_sorry SerrePositivity.localizationComparison_awayMap_bijective_of_power_bounds
assert_no_sorry SerrePositivity.localizationComparisonAwayEquiv
assert_no_sorry SerrePositivity.localizationComparisonAwayEquiv_algebraMap
#print axioms SerrePositivity.localizationComparisonTensorEquiv
#print axioms SerrePositivity.localizationComparisonTensorEquiv_tmul
#print axioms SerrePositivity.localizationComparisonTensorEquiv_comp_tensorMap
#print axioms SerrePositivity.localizationComparison_tensorMap_bijective
#print axioms SerrePositivity.localizationSplitting_common_model_tensorMaps_bijective
#print axioms SerrePositivity.localizationSplitting_common_model_tensor_squares
#print axioms SerrePositivity.localizationComparison_awayMap_bijective_of_power_bounds
#print axioms SerrePositivity.localizationComparisonAwayEquiv
#print axioms SerrePositivity.localizationComparisonAwayEquiv_algebraMap

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST SerrePositivity.DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

-- One actual derived complete finite presentation model supplies all four
-- bijective maps. The choices of E and its maps precede these tests.
theorem audit_actual_complete_common_model_localizations
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Module.Finite R E ∧ Module.FinitePresentation R E ∧
      IsModuleComplete R (p : R) (ModuleCat.of R E) ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        u.toRingHom.Finite ∧ v.toRingHom.Finite ∧
        Function.Bijective (Algebra.TensorProduct.map (AlgHom.id L L) u) ∧
        Function.Bijective (Algebra.TensorProduct.map (AlgHom.id L L) v) ∧
        Function.Bijective (IsLocalization.Away.map
          (Localization.Away (algebraMap R A d))
          (Localization.Away (u (algebraMap R A d))) u.toRingHom (algebraMap R A d)) ∧
        Function.Bijective (IsLocalization.Away.map
          (Localization.Away (algebraMap R (Fin r → R) d))
          (Localization.Away (v (algebraMap R (Fin r → R) d)))
          v.toRingHom (algebraMap R (Fin r → R) d)) := by
  obtain ⟨E, hE, aE, hfinite, _hfp, hmfp, hcR, _hcE, _hcI, _hcQ,
    u, v, w, hu, hv, hloc, huF, hvF, huk, hvk, n, huc, hvc⟩ :=
    localizationSplitting_exists_derivedComplete_common_model p hR d L r e
  let : IsLocalizedModule (.powers d) w.toLinearMap := hloc
  obtain ⟨htu, htv⟩ := localizationSplitting_common_model_tensorMaps_bijective
    (.powers d) L r e u v w hu hv
  have hcu (a : E) : ∃ m : ℕ, d ^ m • a ∈ u.toLinearMap.range := by
    refine ⟨n, (Submodule.Quotient.mk_eq_zero _).mp ?_⟩
    change u.toLinearMap.range.mkQ (d ^ n • a) = 0
    rw [map_smul]
    exact huc _
  have hcv (a : E) : ∃ m : ℕ, d ^ m • a ∈ v.toLinearMap.range := by
    refine ⟨n, (Submodule.Quotient.mk_eq_zero _).mp ?_⟩
    change v.toLinearMap.range.mkQ (d ^ n • a) = 0
    rw [map_smul]
    exact hvc _
  exact ⟨E, hE, aE, hfinite, hmfp, hcR, u, v, huF, hvF, htu, htv,
    localizationComparison_awayMap_bijective_of_power_bounds d u huk hcu,
    localizationComparison_awayMap_bijective_of_power_bounds d v hvk hcv⟩

-- A genuinely noninjective original map is allowed when d=0. The canonical
-- principal localization map is still bijective, with no regularity assumption.
theorem audit_noninjective_original_map_localization
    (R : Type u) [CommRing R] [Nontrivial R] :
    ∃ f : R →ₐ[R] (Fin 0 → R), ¬ Function.Injective f ∧
      Function.Bijective (IsLocalization.Away.map (Localization.Away (0 : R))
        (Localization.Away (f 0)) f.toRingHom 0) := by
  let f : R →ₐ[R] (Fin 0 → R) := Algebra.ofId R (Fin 0 → R)
  refine ⟨f, ?_, ?_⟩
  · intro h
    exact one_ne_zero (h (show f 1 = f 0 from Subsingleton.elim _ _))
  · exact localizationComparison_awayMap_bijective_of_power_bounds 0 f
      (fun a _ => ⟨1, by simp⟩)
      (fun _ => ⟨0, 0, Subsingleton.elim _ _⟩)

assert_no_sorry audit_actual_complete_common_model_localizations
assert_no_sorry audit_noninjective_original_map_localization
#print axioms audit_actual_complete_common_model_localizations
#print axioms audit_noninjective_original_map_localization
