module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower

/-! # A power-divisibility criterion for bounded torsion in an inverse limit -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.DerivedCompletion
variable {R : Type u} [CommRing R] (a : R) (N : ℕ)
    (M : ℕ → Type v) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    (t : ∀ j, M (j + 1) →ₗ[R] M j)

/-- This formulation needs only R-linear relations, so it applies to models
compared with flat quotient modules without transporting module instances. -/
theorem moduleTowerLimit_power_torsion_bound_of_relations
    (hKill : ∀ j, ∀ z : M j, a ^ j • z = 0)
    (hRel : ∀ j m, ∀ z : M (j + m), a ^ m • z = 0 →
      ∃ y : M (j + m), a ^ N • z = a ^ j • y) :
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
  obtain ⟨y, hy⟩ := hRel j m (x.val (j + m)) (congrArg (fun y ↦ y.val (j + m)) hx)
  have he := congrArg (f m) hy
  change a ^ N • x.val j = 0
  simpa only [map_smul, hf, hKill] using he

end SerrePositivity.DerivedCompletion
