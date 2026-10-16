module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.UniformZeroTower
public import SerrePositivity.CommutativeAlgebra.FlatPowerTorsion

/-! # The actual torsion error tower has uniformly zero composites -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.DerivedCompletion
variable {R : Type u} [CommRing R] (a : R) (M : Type v)
    [AddCommGroup M] [Module R M]

/-- The actual kernel of multiplication by the n-th power. -/
abbrev powerTorsionModule (n : ℕ) : Submodule R M :=
  (a ^ n • (LinearMap.id : M →ₗ[R] M)).ker

/-- The error tower transition is multiplication by a, not the inclusion. -/
def powerTorsionTransition (n : ℕ) :
    powerTorsionModule a M (n + 1) →ₗ[R] powerTorsionModule a M n where
  toFun x := ⟨a • (x : M), by
    change a ^ n • (a • (x : M)) = 0
    have hx : a ^ (n + 1) • (x : M) = 0 := x.property
    simpa only [smul_smul, ← pow_succ] using hx⟩
  map_add' x y := by apply Subtype.ext; exact smul_add a (x : M) (y : M)
  map_smul' r x := by
    apply Subtype.ext
    change a • (r • (x : M)) = r • (a • (x : M))
    exact smul_comm a r (x : M)

/-- A composite of k transitions acts by exactly a^k on the original module. -/
theorem powerTorsionComposite_coe (n k : ℕ) (x : powerTorsionModule a M (n + k)) :
    ((moduleTowerComposite R (fun k ↦ ↥(powerTorsionModule a M k))
      (powerTorsionTransition a M)
      n k x : powerTorsionModule a M n) : M) = a ^ k • (x : M) := by
  induction k with
  | zero => simp [moduleTowerComposite]
  | succ k ih =>
    change ((moduleTowerComposite R (fun k ↦ ↥(powerTorsionModule a M k))
      (powerTorsionTransition a M)
      n k (powerTorsionTransition a M (n + k) x) : powerTorsionModule a M n) : M) = _
    rw [ih]
    change a ^ k • (a • (x : M)) = _
    rw [smul_smul, ← pow_succ]

/-- A bound on all power torsion makes the actual error tower uniformly zero. -/
theorem powerTorsionComposite_eq_zero (N : ℕ)
    (h : ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0) (n : ℕ) :
    moduleTowerComposite R (fun k ↦ ↥(powerTorsionModule a M k))
      (powerTorsionTransition a M) n N = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((moduleTowerComposite R (fun k ↦ ↥(powerTorsionModule a M k))
      (powerTorsionTransition a M)
    n N x : powerTorsionModule a M n) : M) = 0
  rw [powerTorsionComposite_coe]
  exact h (n + N) x x.property

/-- For flat coefficients, the ring's bound proves invertibility of the error
tower difference, hence kills its limit and its lim¹. -/
theorem flat_powerTorsionTowerDifference_bijective [Module.Flat R M] (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) :
    Function.Bijective (moduleTowerDifference R (fun k ↦ ↥(powerTorsionModule a M k))
      (powerTorsionTransition a M)) :=
  moduleTowerDifference_bijective_of_uniform_zero R _ _ N
    (powerTorsionComposite_eq_zero a M N (flat_power_torsion_bound a N h))

end SerrePositivity.DerivedCompletion
