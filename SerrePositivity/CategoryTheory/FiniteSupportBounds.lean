module
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Data.Int.Interval

/-! # Finite support from integer bounds -/
public section
namespace SerrePositivity

/-- A function zero outside an integer interval has finite support, for any zero-valued target. -/
lemma finiteSupport_of_bounded_zero {B : Type*} [Zero B] (f : ℤ → B) (a b : ℤ)
    (hf : ∀ q, q < a ∨ b < q → f q = 0) : Function.HasFiniteSupport f := by
  apply (Set.finite_Icc a b).subset
  intro q hq
  by_contra hnot
  exact hq (hf q (by simp only [Set.mem_Icc] at hnot; omega))

end SerrePositivity
