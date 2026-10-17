module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.DoubleFaces
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryOperator
public import SerrePositivity.DifferentialGraded.Quotient.ErasureCancellation

/-! # 二重境界置換の全path直和への包含と有限和の相殺 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

def includeDoubleFace {w : List I} {x y : D} :
    C.DoubleFace A D I w x y → Cochain (C.term A D I w x y) (C.internalHom A D I x y) 2
  | ⟨z, f⟩ => f.comp (Cochain.ofHom (C.inclusion A D I z x y)) (add_zero 2)

lemma includeDoubleFace_negate {w : List I} {x y : D} (f : C.DoubleFace A D I w x y) :
    C.includeDoubleFace A D I (C.negateDoubleFace A D I f) = -C.includeDoubleFace A D I f := by
  rcases f with ⟨z, f⟩
  simp only [includeDoubleFace, negateDoubleFace, Cochain.neg_comp]

def replacementPair (w : List I) (i j : ℕ) (x y : D) :
    Cochain (C.term A D I w x y) (C.internalHom A D I x y) 2 :=
  C.includeDoubleFace A D I (C.doubleFace A D I w i j x y)

lemma replacementPair_swap_of_le (w : List I) (i j : ℕ) (hij : i ≤ j) (x y : D) :
    C.replacementPair A D I w i j x y = -C.replacementPair A D I w (j + 1) i x y := by
  exact (congrArg (C.includeDoubleFace A D I)
    (C.doubleFace_swap_of_le A D I w i j hij x y)).trans (C.includeDoubleFace_negate A D I _)

lemma replacementPair_swap (w : List I) (i j : ℕ) (x y : D) :
    C.replacementPair A D I w i j x y =
    -C.replacementPair A D I w (DGQuotient.swapErasure (i, j)).1
      (DGQuotient.swapErasure (i, j)).2 x y := by
  by_cases hij : j < i
  · have h := C.replacementPair_swap_of_le A D I w j (i - 1) (by omega) x y
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at h
    simp only [DGQuotient.swapErasure, ite_eq_left hij]
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  · simpa only [DGQuotient.swapErasure, Prod.fst, Prod.snd, ite_eq_right hij] using
      C.replacementPair_swap_of_le A D I w i j (by omega) x y

lemma replacementPair_double_sum_zero (w : List I) (x y : D) :
    ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range (w.length - 1),
      C.replacementPair A D I w i j x y = 0 :=
  DGQuotient.erasure_double_sum_cancel w.length (fun i j => C.replacementPair A D I w i j x y)
    (fun i _ j _ => C.replacementPair_swap A D I w i j x y)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
