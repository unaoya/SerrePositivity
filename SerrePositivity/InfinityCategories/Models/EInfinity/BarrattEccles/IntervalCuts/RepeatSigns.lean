module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ActiveRanks

/-!
模型。文献の定義との比較は後で
# 切断を跨ぐ反復文字の二つの削除符号

概要：Berger–Fresse §2.2.7 の辺の両端の符号を同色の二つの削除位置へ結び付ける。
方針：非零切断で同色出現は高々二つなので、後の出現の直前の同色位置を同定する。
規約：前の削除は終点、後の削除は始点の境界項に対応する。
使われ方：切断点を残す非退化な削除項の符号比較。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：反復文字の後の出現より前の同色位置は一つだけ（BF §2.2.7）。
方針：前の同色位置は全て切断点より左なので、左側の単射性を使う。
規約：同色の二つの出現の順序を指定する。
使われ方：最後の出現の削除係数の前出現を固定する。 -/
lemma previousOccurrences_of_repeat {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (a b : Fin l) (hab : a < b) (hu : u a = u b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u b = {a} := by
  have ha := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.repeated_straddles h hab hu).1
  ext j
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hjb, huj⟩
    have hj := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.repeated_straddles h hjb huj).1
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h j a hj.le ha.le (huj.trans hu.symm)
  · rintro rfl
    exact ⟨hab, hu⟩

/-- 概要：切断を跨ぐ同色の二つの削除係数は互いに反対（BF §2.2.7）。
方針：後の出現が最終出現で、その直前の同色位置が前の出現であることを使う。
規約：任意の語で非零な辺切断を持つ場合。
使われ方：辺の始点と終点の境界係数を二つの削除へ一致させる。 -/
lemma deletionCoefficient_repeat_pair {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (a b : Fin l) (hab : a < b) (hu : u a = u b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u b = -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u a := by
  have hb := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.repeated_straddles h hab hu).2
  have hbf : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u b := by
    intro hc
    exact (not_lt_of_ge hb.le) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_pivot h hc)
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.previousOccurrences_of_repeat h a b hab hu
  have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u b).Nonempty := by
    rw [hs]
    exact Finset.singleton_nonempty a
  have hm : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u b).max' hp = a := by
    have hmem := Finset.max'_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u b) hp
    exact Finset.mem_singleton.mp ((Finset.subset_of_eq hs) hmem)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_final u b hbf hp, hm]

/-- 概要：後の反復文字の削除係数は始点側の負の境界符号に一致（BF §2.2.7）。
方針：前の出現での符号比較を反転し、二つの削除係数の反対性を使う。
規約：交換指数は前の出現を除いた元の活動集合で計算する。
使われ方：削除後の活動集合との同定へ接続する右側の符号公式。 -/
lemma edgeSign_final_boundary {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p a b : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) (hab : a < b) (hu : u.val a = u.val b) :
    -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val p * (-1 : ℤ) ^
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < u.val a),
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val b *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p).erase a) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.deletionCoefficient_repeat_pair h a b hab hu, neg_mul]
  exact congrArg Neg.neg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_caesura_boundary u p a h ⟨b, hab, hu.symm⟩)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
