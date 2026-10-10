module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Abelian.Basic

/-! # 短複体の完全性は直和因子に保たれる -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {A : Type*} [Category* A] [Abelian A]

/-- 完全な短複体の retract は完全である。 -/
lemma shortComplex_exact_of_retract {S T : ShortComplex A} (r : Retract S T)
    (hT : T.Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology] at hT ⊢
  let h := r.map (ShortComplex.homologyFunctor A)
  change IsZero ((ShortComplex.homologyFunctor A).obj S)
  rw [IsZero.iff_id_eq_zero, ← h.retract]
  have hz : h.r = 0 := hT.eq_zero_of_src h.r
  rw [hz, comp_zero]

end SerrePositivity
