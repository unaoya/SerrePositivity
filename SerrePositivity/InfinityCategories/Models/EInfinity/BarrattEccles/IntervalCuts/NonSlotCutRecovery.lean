module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SubstitutionCounts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonSlotCut

/-!
模型。文献の定義との比較は後で
# 非切断点色への代入からの外側非零性の復元

概要：Berger–Fresse §2.2.6 の非零合成切断から外側切断の非零性を戻す。
方針：残り色の出現数は保存されるため、指定色の左右の回数だけを別に照合する。
規約：指定色一出現の場合には左右の回数条件は自動的に成立する。
使われ方：二段切断の逆対応における外側非退化性。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：代入後が Nodup なら指定色以外の重複は元にもない（BF §2.2.6）。
方針：残り色の count 保存と Nodup の出現数判定を使う。
規約：指定色の出現回数だけを高々一として追加する。
使われ方：合成切断の各側から外側の各側の Nodup を復元する。 -/
lemma nodup_of_substitute_nodup {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n)))
    (h : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).Nodup) (hk : xs.count k ≤ 1) : xs.Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro a
  by_cases ha : a = k
  · simpa only [ha] using hk
  · rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remaining_count_substitute k ⟨a, ha⟩ xs parts]
    exact List.nodup_iff_count_le_one.mp h _

/-- 概要：指定色の左右の回数条件の下で合成切断の非零性を外側へ戻す（BF §2.2.6）。
方針：合成の左右を代入リストとして評価し、出現数による逆 Nodup 補題を使う。
規約：切断点色は指定色と異なり、指定色は左右それぞれ高々一回。
使われ方：逆対応の全分岐を指定色の共有端点の位置判定へ帰着する。 -/
lemma outer_cut_nondegenerate_of_slot_counts {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp))
    (hleft : ((List.ofFn u.val).take (p.val + 1)).count k ≤ 1)
    (hright : ((List.ofFn u.val).drop p.val).count k ≤ 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_nondegenerate_of_nodup
  · apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nodup_of_substitute_nodup k _ (r.segments v.val) _ hleft
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_prefix u v k r hn p hp]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_prefix_nodup _ _ h
  · apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nodup_of_substitute_nodup k _
      ((r.segments v.val).drop (((List.ofFn u.val).take p.val).count k)) _ hright
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_suffix u v k r hn p hp]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_suffix_nodup _ _ h

/-- 概要：一出現指定色への非零合成切断は外側切断も非零（BF §2.2.6）。
方針：全体で一出現なので左右の部分リストも高々一出現とする。
規約：切断点は指定色以外の外側位置にある。
使われ方：逆対応の内側頂点入力分岐で外側の非零性を供給する。 -/
lemma outer_cut_nondegenerate_of_single_slot {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.outer_cut_nondegenerate_of_slot_counts u v k r hn p hp h
  · exact (List.Sublist.count_le k (List.take_sublist _ _)).trans (Nat.le_of_eq hc)
  · exact (List.Sublist.count_le k (List.drop_sublist _ _)).trans (Nat.le_of_eq hc)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
