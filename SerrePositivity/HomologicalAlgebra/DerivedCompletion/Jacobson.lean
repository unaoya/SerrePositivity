module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison
public import Mathlib.RingTheory.Jacobson.Ideal

/-! # A derived completion parameter lies in the Jacobson radical

Bijectivity of the telescope recurrence supplies geometric series and their
uniqueness, without assuming classical separatedness or regularity.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] (a : R)

/-- A bijective recurrence makes every `1 - a * y` invertible. -/
theorem isUnit_one_sub_mul_of_recurrence_bijective
    (h : Function.Bijective (adicRecurrenceMap a : (ℕ → R) →ₗ[R] (ℕ → R)))
    (y : R) : IsUnit (1 - a * y) := by
  obtain ⟨b, hb⟩ := h.surjective (fun n ↦ y ^ n)
  have hshift : adicRecurrenceMap a (fun n ↦ b (n + 1)) =
      adicRecurrenceMap a (y • b) := by
    rw [map_smul, hb]
    funext n
    have hn := congrFun hb (n + 1)
    simpa only [adicRecurrenceMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, smul_eq_mul, pow_succ, mul_comm] using hn
  have hrec := congrFun (h.injective hshift) 0
  have hzero := congrFun hb 0
  change b 1 = y * b 0 at hrec
  change b 0 - a * b 1 = y ^ 0 at hzero
  rw [hrec, pow_zero] at hzero
  apply isUnit_iff_exists_inv.mpr
  refine ⟨b 0, ?_⟩
  convert hzero using 1; ring

/-- A derived complete ring has its completion parameter in the Jacobson radical. -/
theorem mem_jacobson_bot_of_isModuleComplete
    (h : IsModuleComplete R a (ModuleCat.of R R)) :
    a ∈ Ideal.jacobson (⊥ : Ideal R) := by
  apply Ideal.mem_jacobson_bot.mpr
  intro y
  have hb := (isModuleComplete_iff_recurrence_bijective R a (ModuleCat.of R R)).mp h
  simpa [add_comm] using isUnit_one_sub_mul_of_recurrence_bijective R a hb (-y)

/-- The standard unit criterion for a parameter of a derived complete ring. -/
theorem isUnit_one_sub_mul_of_isModuleComplete
    (h : IsModuleComplete R a (ModuleCat.of R R)) (y : R) :
    IsUnit (1 - a * y) :=
  isUnit_one_sub_mul_of_recurrence_bijective R a
    ((isModuleComplete_iff_recurrence_bijective R a (ModuleCat.of R R)).mp h) y

end SerrePositivity.DerivedCompletion
