module
public import SerrePositivity.DifferentialGraded.Quotient.PrependErasureNaturality
public import SerrePositivity.DifferentialGraded.Quotient.ErasureMiddleInterchange

/-! # 先頭εと非隣接の後方εの消去順序の交換

隣り合う二つのεの場合は、豊穣合成の結合則を用いる別の証明が必要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 先頭εと、それに隣接しない後方εの二重消去は反交換する。 -/
lemma eraseFirst_tail_anticommute {S : Set D} (b c : S) (w : Word S) (i : ℕ) (x y : D) :
    (eraseFirst A D b (c :: w) x y).comp
      (eraseFace A D (c :: w) (i + 1) x y) (show (1 : ℤ) + 1 = 2 by omega) =
    -((eraseFace A D (b :: c :: w) (i + 2) x y).comp
      (eraseFirst A D b ((c :: w).eraseIdx (i + 1)) x y)
      (show (1 : ℤ) + 1 = 2 by omega)) := by
  rw [eraseFirst, eraseFirst, Cochain.comp_assoc_of_second_is_zero_cochain,
    prependMap_eraseFace_succ, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    eraseMiddle_tail_anticommute, Cochain.neg_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
