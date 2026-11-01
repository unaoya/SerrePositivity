module
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Quotient.Erasure

public import Mathlib.Data.ZMod.Basic

/-! # 全微分の構成・後方消去の帰納式・有限和相殺の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

example (K : Complex A) (θ : Cochain K K 1) (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) : Complex A :=
  perturbComplex K θ hθ hθθ
example {S : Set D} (w : Word S) (i : ℕ) (hi : w.length ≤ i) (x y : D) :
    eraseFace A D w i x y = 0 := eraseFace_eq_zero_of_length_le A D w i hi x y
example : swapErasure (0, 0) = (1, 0) := rfl
example : swapErasure (2, 0) = (0, 1) := rfl
example (n : ℕ) (f : ℕ → ℕ → ZMod 2)
    (h : ∀ i < n, ∀ j < n - 1,
      f i j = -f (swapErasure (i, j)).1 (swapErasure (i, j)).2) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - 1), f i j = 0 :=
  erasure_double_sum_cancel n f h

#print axioms closed_one_anticommute
#print axioms square_zero_one_components
#print axioms perturbedDifferential_squared
#print axioms perturbComplex
#print axioms perturbComplex_X
#print axioms perturbComplex_d
#print axioms tensorLeftHom_cochain_comp
#print axioms tensorLeftHom_cochain_anticommute
#print axioms DGQuotient.eraseFace_eq_zero_of_length_le
#print axioms DGQuotient.eraseFace_succ_comp
#print axioms DGQuotient.swapErasure
#print axioms DGQuotient.swapErasure_involutive
#print axioms DGQuotient.swapErasure_ne
#print axioms DGQuotient.swapErasure_mem
#print axioms DGQuotient.erasure_double_sum_cancel
