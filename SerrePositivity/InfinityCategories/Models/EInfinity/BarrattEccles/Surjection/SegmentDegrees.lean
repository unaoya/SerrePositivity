module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapBoundaries
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.LineRanks

/-!
模型。文献の定義との比較は後で
# 分割した内側語の成分次数の総和

概要：Berger–Fresse §1.2.5 の成分次数が元の内側語の次数へ加算されることを証明する。
方針：単調な共有境界の行番号の差を望遠鏡和にし、最後の行番号を使う。
規約：空語の一部分割も別分岐で含める。
使われ方：BF §1.5 の合成語からの d×e 経路の垂直辺数を照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非空語の成分次数は隣接する境界の行番号の差（BF §1.2.5）。
方針：次の開始が現在の末尾であることを代入する。
規約：分割番号は実際の有限添字。
使われ方：成分次数の有限和を望遠鏡和へ直す。 -/
lemma segmentDegree_eq_boundary {n l t : ℕ} (v : Fin l → Fin n)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hl : 0 < l) (i : Fin t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v r i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (r.boundary (i.val + 1)) -
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (r.boundary i.val) := by
  rw [r.boundary_next hl, r.boundary_at]
  rfl

/-- 概要：非空語の全成分次数の和は最後の行番号（BF §1.2.5）。
方針：自然数上の単調な行番号の差を範囲の望遠鏡和として加算する。
規約：分割数と元の語長は正。
使われ方：内側の次数と分割成分の総次数を同定する。 -/
lemma sum_segmentDegree_of_pos {n l t : ℕ} (v : Fin l → Fin n)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (ht : 0 < t) (hl : 0 < l) :
    (∑ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v r i) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (l - 1) := by
  simp_rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree_eq_boundary v r hl]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (r.boundary (i + 1)) - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (r.boundary i)) t]
  have hm : Monotone (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (r.boundary i)) :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_mono v).comp (r.boundary_mono hl)
  rw [Finset.sum_range_tsub hm]
  have hzero : r.boundary 0 = 0 := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, dite_eq_left ht]
    exact r.start_zero ht
  rw [r.boundary_last, hzero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_zero, Nat.sub_zero]

/-- 概要：基底語の全分割成分の次数は元の次数へ加算（BF §1.2.5）。
方針：正の語長では望遠鏡和を使い、空語では次数と全行番号を零にする。
規約：内側 arity 零と次数零の空語も含む。
使われ方：合成保存に使う経路の辺数のうち内側次数 e を供給する。 -/
lemma sum_segmentDegree {n e t : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + e)) (ht : 0 < t) :
    (∑ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val r i) = e := by
  by_cases hl : 0 < n + e
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sum_segmentDegree_of_pos v.val r ht hl, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_last]
  · have hn : n = 0 := by omega
    have he : e = 0 := by omega
    subst n e
    have hz : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v.val p = 0 := by
      intro p
      unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank
      apply Finset.card_eq_zero.mpr
      ext j
      exact Fin.elim0 j
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree, hz, Nat.sub_zero, Finset.sum_const_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
