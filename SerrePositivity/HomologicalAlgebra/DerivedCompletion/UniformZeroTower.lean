module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # A uniform zero composite kills both the limit and the first derived limit -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] (M : ℕ → Type v)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n, M (n + 1) →ₗ[R] M n)

/-- The actual composite of `k` adjacent transition maps. -/
def moduleTowerComposite (n : ℕ) : ∀ k : ℕ, M (n + k) →ₗ[R] M n
  | 0 => LinearMap.id
  | k + 1 => (moduleTowerComposite n k).comp (t (n + k))

/-- Shift along the tower on the full product. -/
def moduleTowerShift : Module.End R (∀ n, M n) where
  toFun x n := t n (x (n + 1))
  map_add' x y := by ext n; exact map_add _ _ _
  map_smul' r x := by ext n; exact map_smul _ _ _

theorem moduleTowerShift_pow_apply (k : ℕ) (x : ∀ n, M n) (n : ℕ) :
    (moduleTowerShift R M t ^ k) x n = moduleTowerComposite R M t n k (x (n + k)) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    change (moduleTowerShift R M t ^ k) (moduleTowerShift R M t x) n = _
    rw [ih]
    rfl

/-- `1-shift` is a unit when all composites of one fixed length vanish. -/
theorem moduleTowerDifference_bijective_of_uniform_zero (N : ℕ)
    (h : ∀ n, moduleTowerComposite R M t n N = 0) :
    Function.Bijective (moduleTowerDifference R M t) := by
  have hn : IsNilpotent (moduleTowerShift R M t) := by
    refine ⟨N, ?_⟩
    ext x n
    rw [moduleTowerShift_pow_apply, h]
    rfl
  have he : moduleTowerDifference R M t = 1 - moduleTowerShift R M t := rfl
  rw [he]
  exact (Module.End.isUnit_iff _).mp hn.isUnit_one_sub

/-- The limit is zero without any surjectivity assumption on the transitions. -/
theorem moduleTowerLimit_subsingleton_of_uniform_zero (N : ℕ)
    (h : ∀ n, moduleTowerComposite R M t n N = 0) :
    Subsingleton (moduleTowerLimit R M t) := by
  have hi := (moduleTowerDifference_bijective_of_uniform_zero R M t N h).1
  refine ⟨fun x y ↦ Subtype.ext (hi (x.property.trans y.property.symm))⟩

end SerrePositivity.DerivedCompletion
