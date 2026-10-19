module
public import SerrePositivity.InfinityCategories.Derived.SpanTwoPrefixCoordinates
public import SerrePositivity.InfinityCategories.DGNerve.EraseReplacementComparison

/-! # A 成分の挿入による三角形右辺の変化

概要：A と後続部分の集合の成分を挿入すると、最上位右辺に符号付きの一項を加える。
方針：その集合を二番目の固定頂点の削除集合と同定する。
規約：HA Proposition 1.3.1.10。使われ方：D7 の最後の三角形方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData
open DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- A 側成分の挿入による三角形右辺の変化は、その成分の変化の符号倍。 -/
lemma spanTwoPrefixRhs_replace_first {n : ℕ} (s : SimplexData R D (n + 3))
    (f : ∀ x y k (hM : 2 ≤ (insert 0 (spanSuffixFaces n)).card),
      x = (insert 0 (spanSuffixFaces n)).min' (Index.nonempty hM) →
      y = (insert 0 (spanSuffixFaces n)).max' (Index.nonempty hM) →
      k = 2 - ((insert 0 (spanSuffixFaces n)).card : ℤ) → GradedHom R (s.obj x) (s.obj y) k) :
    (s.replace (insert 0 (spanSuffixFaces n)) f).spanTwoPrefixRhs - s.spanTwoPrefixRhs =
      ((n : ℤ) + 2).negOnePow •
        (f 0 (Fin.last (n + 3)) (-(n : ℤ) - 2 + 1)
          (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
          (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
          (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; push_cast; omega) -
        s.hom (insert 0 (spanSuffixFaces n)) 0 (Fin.last (n + 3)) (-(n : ℤ) - 2 + 1)
          (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
          (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
          (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; push_cast; omega)) := by
  have H := s.rhs_replace_of_erase_eq Finset.univ 0 (Fin.last (n + 3)) (-(n : ℤ) - 2)
    (by simp) (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
    (spanSecondPrefix n) (Finset.mem_univ _) (spanSecondPrefix_pos n)
    ((spanSecondPrefix_lt_apex n).trans (spanApex_lt_last n))
    (insert 0 (spanSuffixFaces n)) (spanUniv_erase_secondPrefix n)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
    (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; push_cast; omega) f
  simpa only [spanTwoPrefixRhs, spanUniv_sign_secondPrefix] using H

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
