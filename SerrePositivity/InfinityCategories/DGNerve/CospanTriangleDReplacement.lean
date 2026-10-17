module
public import SerrePositivity.InfinityCategories.DGNerve.CospanTrianglePrefixReplacement
public import SerrePositivity.InfinityCategories.DGNerve.EraseReplacementComparison

/-! # D 成分の置換と三角形側右辺の変化

概要：D 側成分の変化は、その負だけ三角形側の右辺を変える。
方針：全体集合の最初の末尾頂点を削除した集合が D 側集合であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：最後の三角形方程式の削除項の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：D 側成分を全体方程式の削除項と同じ次数で読む。
方針：D 側集合の濃度と両端点を指定する。
規約：HA Construction 1.3.1.6。使われ方：D 側の置換による変化の表示。 -/
def cospanTriangleD_Hom {n : ℕ} (s : SimplexData A D (n + 3)) :
    GradedHom A (s.obj 0) (s.obj (cospanLastTail n)) (-(n : ℤ) - 2 + 1) :=
  s.hom (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
    (-(n : ℤ) - 2 + 1)
    (by rw [card_cospanPrefix_insert _
          ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]; omega)
    (cospanPrefix_insert_min _ _)
    (cospanPrefix_insert_max _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _)
    (by rw [card_cospanPrefix_insert _
          ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
        push_cast
        omega)

/-- 概要：D 側の置換による全体右辺の変化は D 側成分の変化の負。
方針：最初の末尾頂点を削除した成分の置換公式と負一符号を使う。
規約：HA Proposition 1.3.1.10。使われ方：二回の置換後の三角形右辺を評価する。 -/
lemma cospanTwoTailRhs_replace_D {n : ℕ} (s : SimplexData A D (n + 3))
    (f : ∀ a b k (hM : 2 ≤ (insert (cospanLastTail n) (cospanPrefixFaces n)).card),
      a = (insert (cospanLastTail n) (cospanPrefixFaces n)).min' (Index.nonempty hM) →
      b = (insert (cospanLastTail n) (cospanPrefixFaces n)).max' (Index.nonempty hM) →
      k = 2 - ((insert (cospanLastTail n) (cospanPrefixFaces n)).card : ℤ) →
      GradedHom A (s.obj a) (s.obj b) k) :
    (s.replace (insert (cospanLastTail n) (cospanPrefixFaces n)) f).cospanTwoTailRhs -
        s.cospanTwoTailRhs =
      -(f 0 (cospanLastTail n) (-(n : ℤ) - 2 + 1)
          (by rw [card_cospanPrefix_insert _
                ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]; omega)
          (cospanPrefix_insert_min _ _)
          (cospanPrefix_insert_max _
            ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _)
          (by rw [card_cospanPrefix_insert _
                ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
              push_cast
              omega) - s.cospanTriangleD_Hom) := by
  have hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hk : -(n : ℤ) - 2 = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ) := by
    simp only [Finset.card_univ, Fintype.card_fin]
    push_cast
    omega
  have H := s.rhs_replace_of_erase_eq Finset.univ 0 (cospanLastTail n) (-(n : ℤ) - 2)
    hI (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _) hk
    (cospanFirstTail n) (Finset.mem_univ _)
    ((cospanApex_pos n).trans (cospanApex_lt_firstTail n)) (cospanFirstTail_lt_lastTail n)
    (insert (cospanLastTail n) (cospanPrefixFaces n)) (cospanUniv_erase_firstTail n)
    (by rw [card_cospanPrefix_insert _
          ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]; omega)
    (cospanPrefix_insert_min _ _)
    (cospanPrefix_insert_max _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _)
    (by rw [card_cospanPrefix_insert _
          ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
        push_cast
        omega) f
  simpa only [cospanUniv_sign_firstTail, Units.neg_smul, one_smul,
    cospanTwoTailRhs, cospanTriangleD_Hom] using H

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
