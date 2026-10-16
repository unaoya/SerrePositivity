import SerrePositivity.HomologicalAlgebra.DerivedCompletion.UniformZeroTower
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.UniformZeroTowerHomology
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTower
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionComplex
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

-- Actual error tower and uniformly zero transition composites.
assert_no_sorry moduleTowerComposite
#print axioms moduleTowerComposite
assert_no_sorry moduleTowerShift
#print axioms moduleTowerShift
assert_no_sorry moduleTowerShift_pow_apply
#print axioms moduleTowerShift_pow_apply
assert_no_sorry moduleTowerDifference_bijective_of_uniform_zero
#print axioms moduleTowerDifference_bijective_of_uniform_zero
assert_no_sorry moduleTowerLimit_subsingleton_of_uniform_zero
#print axioms moduleTowerLimit_subsingleton_of_uniform_zero
assert_no_sorry complexTowerComposite
#print axioms complexTowerComposite
assert_no_sorry complexTowerComposite_homology
#print axioms complexTowerComposite_homology
assert_no_sorry complexTowerHolim_homology_isZero_of_uniform_zero
#print axioms complexTowerHolim_homology_isZero_of_uniform_zero
assert_no_sorry complexTowerHolim_acyclic_of_uniform_zero
#print axioms complexTowerHolim_acyclic_of_uniform_zero
assert_no_sorry powerTorsionModule
#print axioms powerTorsionModule
assert_no_sorry powerTorsionTransition
#print axioms powerTorsionTransition
assert_no_sorry powerTorsionComposite_coe
#print axioms powerTorsionComposite_coe
assert_no_sorry powerTorsionComposite_eq_zero
#print axioms powerTorsionComposite_eq_zero
assert_no_sorry flat_powerTorsionTowerDifference_bijective
#print axioms flat_powerTorsionTowerDifference_bijective
assert_no_sorry powerTorsionComplex
#print axioms powerTorsionComplex
assert_no_sorry powerTorsionComplexTransition
#print axioms powerTorsionComplexTransition
assert_no_sorry powerTorsionComplexComposite_coe
#print axioms powerTorsionComplexComposite_coe
assert_no_sorry powerTorsionComplex_holim_acyclic
#print axioms powerTorsionComplex_holim_acyclic

-- No upper or lower bound on K is required for the error tower itself.
example {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : ∀ i, Module.Flat R (K.X i))
    (N : ℕ) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) :
    (complexTowerHomotopyLimit R (powerTorsionComplex a K)
      (powerTorsionComplexTransition a K)).Acyclic :=
  powerTorsionComplex_holim_acyclic a K hK N h

-- Length zero is included when the hypothesis really makes the stages zero.
example {R : Type u} [CommRing R] (M : ℕ → Type v)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n, M (n + 1) →ₗ[R] M n)
    (h : ∀ n, moduleTowerComposite R M t n 0 = 0) :
    Function.Bijective (moduleTowerDifference R M t) :=
  moduleTowerDifference_bijective_of_uniform_zero R M t 0 h
