import SerrePositivity.CommutativeAlgebra.LocalizationComparisonBounds
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.localizationComparison_coker_power_torsion_of_localized_target
assert_no_sorry SerrePositivity.localizationComparison_exists_pow_annihilates_coker_of_localized_target
assert_no_sorry SerrePositivity.localizationComparisons_exists_common_pow_annihilates_cokers_of_localized_target
#print axioms SerrePositivity.localizationComparison_coker_power_torsion_of_localized_target
#print axioms SerrePositivity.localizationComparison_exists_pow_annihilates_coker_of_localized_target
#print axioms SerrePositivity.localizationComparisons_exists_common_pow_annihilates_cokers_of_localized_target

noncomputable section
open SerrePositivity

-- Inverting zero gives a legitimate localization with a noninjective map.
-- The comparison itself is zero and has a nonzero cokernel over a nonzero ring.
theorem audit_noninjective_localized_target
    (R : Type) [CommRing R] [Nontrivial R] :
    let Z := Fin 0 → R
    let v : R →ₗ[R] Z := 0
    let f : R →ₗ[R] R := 0
    ¬ Function.Injective v ∧
      (∃ y : R ⧸ f.range, y ≠ 0) ∧
      ∃ n : ℕ, ∀ y : R ⧸ f.range, (0 : R) ^ n • y = 0 := by
  let Z := Fin 0 → R
  let v : R →ₗ[R] Z := 0
  let f : R →ₗ[R] R := 0
  change ¬ Function.Injective v ∧ (∃ y : R ⧸ f.range, y ≠ 0) ∧ _
  let : IsLocalizedModule (.powers (0 : R)) v := {
    map_units := fun s => by
      have h : algebraMap R (Module.End R Z) (s : R) = 1 := Subsingleton.elim _ _
      rw [h]
      exact isUnit_one
    surj := fun y => ⟨(0, 1), Subsingleton.elim _ _⟩
    exists_of_eq := fun _ => by
      refine ⟨⟨(0 : R), ?_⟩, ?_⟩
      · exact ⟨1, pow_one (0 : R)⟩
      · simp only [Submonoid.smul_def, zero_smul] }
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact one_ne_zero (h (show v 1 = v 0 from Subsingleton.elim _ _))
  · refine ⟨f.range.mkQ 1, ?_⟩
    intro h
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero f.range).mp h
    exact zero_ne_one (show (0 : R) = 1 from hx)
  · exact localizationComparison_exists_pow_annihilates_coker_of_localized_target
      0 f v v (Subsingleton.elim _ _)

assert_no_sorry audit_noninjective_localized_target
#print axioms audit_noninjective_localized_target
