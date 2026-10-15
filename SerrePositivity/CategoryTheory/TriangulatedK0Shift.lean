module
public import SerrePositivity.CategoryTheory.TriangulatedK0
public import Mathlib.Algebra.Ring.NegOnePow

/-! # Integer shifts in the Grothendieck group of a pretriangulated category -/
@[expose] public noncomputable section
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
namespace TriangulatedK0
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
/-- Integer shifts multiply Grothendieck classes by the corresponding sign. -/
lemma mk_shift (X : C) (n : ℤ) : mk (X⟦n⟧) = ((n.negOnePow : ℤˣ) : ℤ) • mk X := by
  induction n using Int.induction_on with
  | zero =>
    rw [Int.negOnePow_zero, Units.val_one, one_smul]
    exact mk_iso ((shiftFunctorZero C ℤ).app X)
  | succ n ih =>
    have h := mk_iso ((shiftFunctorAdd' C (n : ℤ) 1 (n + 1) rfl).app X)
    simp only [Functor.comp_obj] at h
    rw [h, mk_shift_one, ih, Int.negOnePow_succ, Units.val_neg, neg_smul]
  | pred n ih =>
    have h := mk_iso ((shiftFunctorAdd' C (-n - 1 : ℤ) 1 (-n) (by omega)).app X)
    simp only [Functor.comp_obj] at h
    rw [mk_shift_one, ih] at h
    rw [← neg_neg (mk (X⟦(-n - 1 : ℤ)⟧)), ← h, Int.negOnePow_sub,
      Int.negOnePow_one, mul_neg, mul_one, Units.val_neg, neg_smul]
end TriangulatedK0
end SerrePositivity
