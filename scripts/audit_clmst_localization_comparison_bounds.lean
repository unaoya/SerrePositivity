import SerrePositivity.CommutativeAlgebra.FiniteCommonLocalizationBounds
import SerrePositivity.CommutativeAlgebra.DoubleLocalizationTensorComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.exists_uniform_power_smul_eq_zero_of_finite
assert_no_sorry SerrePositivity.localizationComparison_ker_power_torsion
assert_no_sorry SerrePositivity.localizationComparison_exists_pow_annihilates_coker
assert_no_sorry SerrePositivity.localizationComparisons_exists_common_pow_annihilates_cokers
assert_no_sorry SerrePositivity.localizationSplitting_exists_finite_common_model_bounds
#print axioms SerrePositivity.exists_uniform_power_smul_eq_zero_of_finite
#print axioms SerrePositivity.localizationComparison_ker_power_torsion
#print axioms SerrePositivity.localizationComparison_exists_pow_annihilates_coker
#print axioms SerrePositivity.localizationComparisons_exists_common_pow_annihilates_cokers
#print axioms SerrePositivity.localizationSplitting_exists_finite_common_model_bounds

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open SerrePositivity
open scoped TensorProduct

-- The original double localization gives one conductor exponent for both actual algebra maps.
theorem audit_actual_double_localization_common_conductor
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (g : R) (f : Localization.Away g) (r : ℕ) :
    letI := GenericEtale.awayAlgebra R A g
    ∀ e : (Localization.Away f) ⊗[Localization.Away g]
      (Localization.Away (algebraMap R A g)) ≃ₐ[Localization.Away f]
        (Fin r → Localization.Away f),
    ∃ E : Subalgebra R (Fin r → Localization.Away f), Module.Finite R E ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        (∀ a, E.val (u a) = e ((1 : Localization.Away f) ⊗ₜ[Localization.Away g]
          algebraMap A (Localization.Away (algebraMap R A g)) a)) ∧
        (∀ b i, E.val (v b) i = algebraMap R (Localization.Away f) (b i)) ∧
        ∃ n : ℕ, ∀ z : E,
          (g * (IsLocalization.Away.sec g f).1) ^ n • z ∈ u.toLinearMap.range ∧
          (g * (IsLocalization.Away.sec g f).1) ^ n • z ∈ v.toLinearMap.range := by
  letI := GenericEtale.awayAlgebra R A g
  intro e
  let d := g * (IsLocalization.Away.sec g f).1
  let : IsLocalization (.powers d) (Localization.Away f) :=
    principalLocalizationTower_isLocalization g f
  let e' := (doubleLocalizationTensorEquiv R A g f).trans e
  obtain ⟨E, hfinite, _hloc, u, v, hu, hv, _huF, _hvF, _huk, _hvk, n, hn, hn'⟩ :=
    localizationSplitting_exists_finite_common_model_bounds d (Localization.Away f) r e'
  refine ⟨E, hfinite, u, v, ?_, hv, n, ?_⟩
  · intro a
    rw [hu]
    change e (doubleLocalizationTensorEquiv R A g f ((1 : Localization.Away f) ⊗ₜ[R] a)) = _
    rw [doubleLocalizationTensorEquiv_tmul]
  · intro z
    constructor
    · apply (Submodule.Quotient.mk_eq_zero (R := R) (M := E) u.toLinearMap.range).mp
      change u.toLinearMap.range.mkQ (d ^ n • z) = 0
      rw [map_smul]
      exact hn _
    · apply (Submodule.Quotient.mk_eq_zero (R := R) (M := E) v.toLinearMap.range).mp
      change v.toLinearMap.range.mkQ (d ^ n • z) = 0
      rw [map_smul]
      exact hn' _

-- The original zero-rank case keeps both cokernels zero in every exponent.
theorem audit_zero_rank_common_model_cokernels
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (e : L ⊗[R] A ≃ₐ[L] (Fin 0 → L)) :
    ∃ E : Subalgebra R (Fin 0 → L), Module.Finite R E ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin 0 → R) →ₐ[R] E),
        ∀ n : ℕ, (∀ y : E ⧸ u.toLinearMap.range, d ^ n • y = 0) ∧
          (∀ y : E ⧸ v.toLinearMap.range, d ^ n • y = 0) := by
  obtain ⟨E, hfinite, _hloc, u, v, _⟩ :=
    localizationSplitting_exists_finite_common_model_bounds d L 0 e
  exact ⟨E, hfinite, u, v, fun _ => ⟨fun _ => Subsingleton.elim _ _,
    fun _ => Subsingleton.elim _ _⟩⟩

assert_no_sorry audit_actual_double_localization_common_conductor
assert_no_sorry audit_zero_rank_common_model_cokernels
#print axioms audit_actual_double_localization_common_conductor
#print axioms audit_zero_rank_common_model_cokernels
