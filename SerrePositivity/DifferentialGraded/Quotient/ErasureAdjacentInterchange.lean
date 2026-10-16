module
public import SerrePositivity.DifferentialGraded.Quotient.PrependFirstNaturality
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFaceEquations
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFirstTailInterchange

/-! # 隣接する先頭二つのεの二重消去の反交換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma eraseFirst_adjacent_anticommute {S : Set D} (b c : S) (w : Word S) (x y : D) :
    (eraseFirst A D b (c :: w) x y).comp
      (eraseFirst A D c w x y) (show (1 : ℤ) + 1 = 2 by omega) =
    -((eraseFace A D (b :: c :: w) 1 x y).comp
      (eraseFirst A D b w x y) (show (1 : ℤ) + 1 = 2 by omega)) := by
  change ((eraseMiddle A (homObject A D x b.val) (term A D (c :: w) b.val y)).comp
    (Cochain.ofHom (prependMap A D (c :: w) x b.val y)) (add_zero 1)).comp
      (eraseFirst A D c w x y) (by omega) =
    -((eraseFace A D (b :: c :: w) 1 x y).comp
      ((eraseMiddle A (homObject A D x b.val) (term A D w b.val y)).comp
        (Cochain.ofHom (prependMap A D w x b.val y)) (add_zero 1)) (by omega))
  rw [Cochain.comp_assoc_of_second_is_zero_cochain,
    prependMap_eraseFirst, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    eraseMiddle_tail_anticommute, Cochain.neg_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain]
  rfl

/-- 先頭εと任意の後方位置の消去は反交換する。範囲外の位置も含む。 -/
lemma eraseFirst_face_anticommute {S : Set D} (b : S) (w : Word S) (i : ℕ) (x y : D) :
    (eraseFirst A D b w x y).comp (eraseFace A D w i x y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -((eraseFace A D (b :: w) (i + 1) x y).comp
      (eraseFirst A D b (w.eraseIdx i) x y) (show (1 : ℤ) + 1 = 2 by omega)) := by
  cases w with
  | nil =>
    simp only [eraseFace_cons_succ, eraseFace_nil, map_zero,
      Cochain.comp_zero, Cochain.zero_comp, neg_zero]
  | cons c w =>
    cases i with
    | zero => exact eraseFirst_adjacent_anticommute A D b c w x y
    | succ i => exact eraseFirst_tail_anticommute A D b c w i x y

end SerrePositivity.DifferentialGraded.DGQuotient
