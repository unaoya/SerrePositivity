module

public import SerrePositivity.CommutativeAlgebra.FlatPowerQuotientTorsion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower

/-! # The inverse limit of flat power residues has bounded power torsion

No surjectivity of the transition maps is required for this bound.
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.DerivedCompletion
variable {R : Type u} [CommRing R] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (M : ℕ → Type v) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    [∀ j, Module (R ⧸ Ideal.span {a ^ j}) (M j)]
    [∀ j, IsScalarTower R (R ⧸ Ideal.span {a ^ j}) (M j)]
    [∀ j, Module.Flat (R ⧸ Ideal.span {a ^ j}) (M j)]
    (t : ∀ j, M (j + 1) →ₗ[R] M j)
include h

/-- The original coefficient bound works unchanged on the inverse limit of
arbitrary compatible flat modules over the standard power quotients. -/
theorem moduleTowerLimit_flat_residues_power_torsion_bound :
    ∀ m : ℕ, ∀ x : moduleTowerLimit R M t, a ^ m • x = 0 → a ^ N • x = 0 := by
  intro m x hx
  apply Subtype.ext
  funext j
  let f : ∀ k : ℕ, M (j + k) →ₗ[R] M j := fun k ↦
    Nat.rec (motive := fun k ↦ M (j + k) →ₗ[R] M j) LinearMap.id
      (fun k g ↦ g.comp (t (j + k))) k
  have hf : ∀ k, f k (x.val (j + k)) = x.val j := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change f k (t (j + k) (x.val (j + k + 1))) = x.val j
      rw [(mem_moduleTowerLimit_iff R M t _).mp x.property (j + k), ih]
  have hxm : a ^ m • x.val (j + m) = 0 := congrArg (fun y ↦ y.val (j + m)) hx
  have hxm' : (Ideal.Quotient.mk (Ideal.span {a ^ (j + m)}) a) ^ m •
      x.val (j + m) = 0 := by
    simpa only [← map_pow, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] using hxm
  obtain ⟨y, hy⟩ := flat_powerQuotient_torsion_relation a N h j m (M (j + m)) _ hxm'
  have hy' : a ^ N • x.val (j + m) = a ^ j • y := by
    simpa only [← map_pow, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] using hy
  have hj : ∀ z : M j, a ^ j • z = 0 := by
    intro z
    rw [← algebraMap_smul (R ⧸ Ideal.span {a ^ j}) (a ^ j) z]
    have hz : algebraMap R (R ⧸ Ideal.span {a ^ j}) (a ^ j) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _)
    rw [hz, zero_smul]
  have he := congrArg (f m) hy'
  change a ^ N • x.val j = 0
  simpa only [map_smul, hf, hj] using he

end SerrePositivity.DerivedCompletion
