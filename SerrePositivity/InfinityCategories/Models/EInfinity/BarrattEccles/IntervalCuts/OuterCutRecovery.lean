module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SegmentBoundaryCuts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonSlotCutRecovery

/-!
模型。文献の定義との比較は後で
# 残りラベルの合成位置からの外側切断の復元

概要：Berger–Fresse §2.2.6 の残りラベル切断点では外側切断も非零となる。
方針：外側位置と挿入部分語の順序を照合し、共有端点の跨ぎで指定色を左右へ分ける。
規約：外側指定色の出現数を追加仮定しない。
使われ方：有限対応の逆方向の残りラベル分岐。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定出現より前の外側位置はその挿入部分語の先頭より前（BF §2.2.6）。
方針：外側一文字直後の代入長を指定出現直前の代入長で抑える。
規約：外側位置は指定色ではない。
使われ方：合成切断点の順序制約を外側位置へ戻す。 -/
lemma compositeOuterPosition_lt_segmentFirst {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k))
    (hi : p < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentFirst u v k r hn i := by
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_mono k (List.ofFn u.val) (r.segments v.val)
    (show p.val + 1 ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val from hi)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_take_at_non_slot u.val k p hp, List.length_append,
    List.length_singleton] at H
  simp only [Fin.lt_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentFirst,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition]
  omega

/-- 概要：指定出現より後の外側位置はその挿入部分語の末尾より後（BF §2.2.6）。
方針：指定出現直後の代入長を外側位置直前の代入長で抑える。
規約：挿入部分語は正長。
使われ方：共有端点より前後という条件を元の指定出現へ戻す。 -/
lemma compositeSegmentLast_lt_outerPosition {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k))
    (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i < p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentLast u v k r hn i < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp := by
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_mono k (List.ofFn u.val) (r.segments v.val)
    (show (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val + 1 ≤ p.val from hi)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_at_occurrence] at H
  have := r.positive (show 0 < n + e by omega) i
  simp only [Fin.lt_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentLast,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition]
  omega

/-- 概要：残り位置の非零合成切断では指定色は元の左右に高々一回（BF §2.2.6）。
方針：二出現なら共有端点の跨ぎを外側位置へ戻し、一出現なら全体の回数で抑える。
規約：切断点自身は指定色ではない。
使われ方：外側切断の非退化性を無条件に復元する。 -/
lemma slot_counts_of_compositeOuterPosition_cut {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp)) :
    ((List.ofFn u.val).take (p.val + 1)).count k ≤ 1 ∧
      ((List.ofFn u.val).drop p.val).count k ≤ 1 := by
  have hle := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.slot_occurrenceCount_le_two_of_composite_cut u v k r hn _ h
  by_cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1
  · exact ⟨(List.Sublist.count_le k (List.take_sublist _ _)).trans (Nat.le_of_eq hc),
      (List.Sublist.count_le k (List.drop_sublist _ _)).trans (Nat.le_of_eq hc)⟩
  have hpos := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k
  have hc2 : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 2 := by omega
  let i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) := ⟨0, by omega⟩
  let j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) := ⟨1, by omega⟩
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegment_boundary_straddles u v k r hn _ h i j rfl
  have hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i < p := by
    by_contra hnot
    rcases lt_or_eq_of_le (le_of_not_gt hnot) with hpi | he
    · have K := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_lt_segmentFirst u v k r hn p hp i hpi
      have hfl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentFirst u v k r hn i ≤
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentLast u v k r hn i := by
        change _ + 0 ≤ _ + ((r.val i).val - 1)
        omega
      exact (lt_irrefl _) (lt_trans K (lt_of_le_of_lt hfl H.1))
    · exact hp (he ▸ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k i)
  have hj : p < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j := by
    by_contra hnot
    rcases lt_or_eq_of_le (le_of_not_gt hnot) with hjp | he
    · have K := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentLast_lt_outerPosition u v k r hn p hp j hjp
      have hfl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentFirst u v k r hn j ≤
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentLast u v k r hn j := by
        change _ + 0 ≤ _ + ((r.val j).val - 1)
        omega
      exact (lt_irrefl _) (lt_trans H.2 (lt_of_le_of_lt hfl K))
    · exact hp (he.symm ▸ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k j)
  constructor
  · have K := List.Sublist.count_le k (List.take_sublist_take_left (l := List.ofFn u.val)
      (show p.val + 1 ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j).val from hj))
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_count_take] at K
    exact K
  · have K := List.Sublist.count_le k (List.take_sublist_take_left (l := List.ofFn u.val)
      (show (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val + 1 ≤ p.val from hi))
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_count_take_succ] at K
    have T := congrArg (List.count k) (List.take_append_drop p.val (List.ofFn u.val))
    rw [List.count_append] at T
    change _ + _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k at T
    rw [hc2] at T
    change 0 + 1 ≤ _ at K
    omega

/-- 概要：残り位置の非零合成切断から外側の非零切断を復元（BF §2.2.6）。
方針：共有端点から導出した指定色の左右回数と、残り色の出現数保存を使う。
規約：外側の非零性を追加仮定しない。
使われ方：有限全単射の残りラベル分岐の外側条件。 -/
lemma outer_cut_nondegenerate_of_compositeOuterPosition {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p := by
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.slot_counts_of_compositeOuterPosition_cut u v k r hn p hp h
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.outer_cut_nondegenerate_of_slot_counts u v k r hn p hp h H.1 H.2

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
