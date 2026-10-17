import SerrePositivity.CLMST.Prop247Uniform
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.moduleMapConeScalar_of_surjective_source
assert_no_sorry SerrePositivity.CLMST.prop247_fixed_cone_of_scaled_common_comparison
assert_no_sorry SerrePositivity.CLMST.prop247_fixed_cone_of_common_comparison
assert_no_sorry SerrePositivity.CLMST.prop247_uniform_reductions_of_fixed_cone
assert_no_sorry SerrePositivity.CLMST.prop247_uniform_of_common_comparison
#print axioms SerrePositivity.moduleMapConeScalar_of_surjective_source
#print axioms SerrePositivity.CLMST.prop247_fixed_cone_of_scaled_common_comparison
#print axioms SerrePositivity.CLMST.prop247_fixed_cone_of_common_comparison
#print axioms SerrePositivity.CLMST.prop247_uniform_reductions_of_fixed_cone
#print axioms SerrePositivity.CLMST.prop247_uniform_of_common_comparison

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.CLMST
attribute [local instance] HasDerivedCategory.standard

-- A specified finite-free comparison is recovered from the common-object API.
-- Rank zero is included by r = 0; g may be a zero divisor or zero.
theorem audit_prop247_common_identity
    (B : Type u) [CommRing B] [IsReduced B]
    (L : Type u) [AddCommGroup L] [Module B L] [Module.Finite B L]
    (g : B) (r : ℕ) (u : L →ₗ[B] (Fin r → B))
    (hu : Function.Bijective (awayModuleMap g u)) :
    ∃ q : ℕ, moduleMapConeScalar B u (g ^ q) = 0 := by
  apply prop247_fixed_cone_of_common_comparison g r u u LinearMap.id LinearMap.id rfl hu
  · intro y hy
    change y = 0 at hy
    rw [hy, smul_zero]
  · intro y hy
    change y = 0 at hy
    rw [hy, smul_zero]
  · intro y
    obtain ⟨y, rfl⟩ := (LinearMap.id : (Fin r → B) →ₗ[B] (Fin r → B)).range.mkQ_surjective y
    have hz : (LinearMap.id : (Fin r → B) →ₗ[B] (Fin r → B)).range.mkQ y = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩
    rw [hz, smul_zero]


assert_no_sorry audit_prop247_common_identity
#print axioms audit_prop247_common_identity

-- The concrete rank-zero free module, including the zero ring.
theorem audit_prop247_rank_zero
    (B : Type u) [CommRing B] [IsReduced B] (g : B) :
    ∃ q : ℕ, moduleMapConeScalar B
      (LinearMap.id : (Fin 0 → B) →ₗ[B] (Fin 0 → B)) (g ^ q) = 0 := by
  apply audit_prop247_common_identity B (Fin 0 → B) g 0 LinearMap.id
  rw [awayModuleMap, IsLocalizedModule.map_id]
  exact ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

assert_no_sorry audit_prop247_rank_zero
#print axioms audit_prop247_rank_zero
