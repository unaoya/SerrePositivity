import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FlatResidueLimitTorsion
import Mathlib.Util.AssertNoSorry

open SerrePositivity SerrePositivity.DerivedCompletion

assert_no_sorry smul_eq_zero_of_flat_of_mul_kernel
#print axioms smul_eq_zero_of_flat_of_mul_kernel
assert_no_sorry flat_power_torsion_bound
#print axioms flat_power_torsion_bound
assert_no_sorry smul_eq_smul_of_flat_of_mul_kernel
#print axioms smul_eq_smul_of_flat_of_mul_kernel
assert_no_sorry powerQuotient_mul_kernel_relation
#print axioms powerQuotient_mul_kernel_relation
assert_no_sorry flat_powerQuotient_torsion_relation
#print axioms flat_powerQuotient_torsion_relation
assert_no_sorry moduleTowerLimit_flat_residues_power_torsion_bound
#print axioms moduleTowerLimit_flat_residues_power_torsion_bound

-- The same bound, with no prime, regularity, or finite generation hypotheses.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (a : R) (N : ℕ) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) :
    ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0 :=
  flat_power_torsion_bound a N h

-- A zero torsion bound is allowed when supplied by the ring itself.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (a : R) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → r = 0)
    (n : ℕ) (x : M) (hx : a ^ n • x = 0) : x = 0 := by
  simpa using flat_power_torsion_bound a 0 (by simpa using h) n x hx

-- Arbitrary universes, arbitrary transitions, and the actual standard quotient actions.
universe u v
example {R : Type u} [CommRing R] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (M : ℕ → Type v) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    [∀ j, Module (R ⧸ Ideal.span {a ^ j}) (M j)]
    [∀ j, IsScalarTower R (R ⧸ Ideal.span {a ^ j}) (M j)]
    [∀ j, Module.Flat (R ⧸ Ideal.span {a ^ j}) (M j)]
    (t : ∀ j, M (j + 1) →ₗ[R] M j) :
    ∀ m : ℕ, ∀ x : moduleTowerLimit R M t, a ^ m • x = 0 → a ^ N • x = 0 :=
  moduleTowerLimit_flat_residues_power_torsion_bound a N h M t
