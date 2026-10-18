module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalFace

/-!
# shuffle の終端の境界面

概要：Berger–Fresse §1.1.3 の shuffle の終端の面を、最後の辺の向きに応じて同定する。
方針：最後の辺を削除すると、残る頂点では削除位置をまだ通過していないことを使う。
規約：終端の水平辺は第一の入力の最後の面、垂直辺は第二の入力の最後の面に対応する。
使われ方：shuffle の Leibniz 則の右端の境界項を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：最後の水平辺を削除した面の水平座標は第一の入力の最後の頂点を避ける（Berger–Fresse §1.1.3）。
方針：残った頂点は削除辺を通過しないので座標の増分が零となる。
規約：hlast は a が最後の辺であることを値の等式で表す。
使われ方：終端が水平である場合の面を比較する。 -/
lemma horizontalDeletion_last {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (ha : a ∈ s.val) (hlast : a.val + 1 = p + 1 + q)
    (k : Fin (p + 1 + q)) :
    s.horizontal (a.succ.succAbove k) =
      (Fin.last (p + 1)).succAbove
        (((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).horizontal
          (Fin.cast (by omega : p + 1 + q = p + q + 1) k)) := by
  have hv := horizontalDeletion_horizontal_val s a ha k
  have hk : ¬ a.val < k.val := by have h := k.isLt; omega
  rw [ite_eq_right hk] at hv
  apply Fin.ext
  rw [Fin.succAbove_last]
  exact hv

/-- 概要：最後の垂直辺を削除した面の垂直座標は第二の入力の最後の頂点を避ける（Berger–Fresse §1.1.3）。
方針：削除位置を通過しない残りの頂点の座標公式を使う。
規約：削除した辺は水平辺集合に属さない。
使われ方：終端が垂直である場合の面を比較する。 -/
lemma verticalDeletion_last {p q : ℕ} (s : ShufflePath p (q + 1))
    (a : Fin (p + (q + 1))) (ha : a ∉ s.val) (hlast : a.val + 1 = p + (q + 1))
    (k : Fin (p + q + 1)) :
    s.vertical (a.succ.succAbove k) =
      (Fin.last (q + 1)).succAbove
        (((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).vertical k) := by
  have hv := verticalDeletion_vertical_val s a ha k
  have hk : ¬ a.val < k.val := by have h := k.isLt; omega
  rw [ite_eq_right hk] at hv
  apply Fin.ext
  rw [Fin.succAbove_last]
  exact hv

/-- 概要：最後の辺が水平である shuffle の終端面は第一の入力の最後の面から得られる（Berger–Fresse §1.1.3）。
方針：水平座標の終端の公式と垂直座標の保存を各頂点へ適用する。
規約：水平面の次数移送には horizontalFaceMap を使う。
使われ方：Leibniz 則の第一の入力の最後の境界項を同定する。 -/
lemma shuffleSimplex_horizontal_last_face (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath (p + 1) q) (a : Fin (p + 1 + q)) (ha : a ∈ s.val)
    (hlast : a.val + 1 = p + 1 + q)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    (simplicial (m + n)).map (horizontalFaceMap p q a).op
        (shuffleSimplex m n i (p := p + 1) (q := q) s x y) =
      shuffleSimplex m n i (p := p) (q := q) ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩)
        ((simplicial (m + 1)).δ (Fin.last (p + 1)) x) y := by
  apply (simplexEquiv (m + n) (p + q)).injective
  funext k
  simp only [simplexEquiv_map, simplexEquiv_shuffleSimplex, simplexEquiv_δ]
  let l := Fin.cast (by omega : p + q + 1 = p + 1 + q) k
  have hcast : Fin.cast (by omega : p + 1 + q = p + q + 1) l = k := Fin.ext rfl
  change permutationComposition m n i
      (simplexEquiv (m + 1) (p + 1) x (s.horizontal (a.succ.succAbove l)))
      (simplexEquiv n q y (s.vertical (a.succ.succAbove l))) = _
  rw [horizontalDeletion_last s a ha hlast l, horizontalDeletion_vertical s a ha l, hcast]

/-- 概要：最後の辺が垂直である shuffle の終端面は第二の入力の最後の面から得られる（Berger–Fresse §1.1.3）。
方針：水平座標の保存と垂直座標の終端の公式を各頂点へ適用する。
規約：元の shuffle の終端面は δ a.succ で表す。
使われ方：Leibniz 則の第二の入力の最後の境界項を同定する。 -/
lemma shuffleSimplex_vertical_last_face (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath p (q + 1)) (a : Fin (p + (q + 1))) (ha : a ∉ s.val)
    (hlast : a.val + 1 = p + (q + 1))
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (simplicial (m + n)).δ a.succ (shuffleSimplex m n i (p := p) (q := q + 1) s x y) =
      shuffleSimplex m n i (p := p) (q := q) ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩) x
        ((simplicial n).δ (Fin.last (q + 1)) y) := by
  apply (simplexEquiv (m + n) (p + q)).injective
  funext k
  erw [simplexEquiv_δ (m + n) (p + q),
    simplexEquiv_shuffleSimplex m n i (p := p) (q := q + 1)]
  simp only [simplexEquiv_δ, simplexEquiv_shuffleSimplex]
  rw [verticalDeletion_horizontal s a ha k, verticalDeletion_last s a ha hlast k]

end SerrePositivity.EInfinity.BarrattEccles
