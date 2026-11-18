module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotActivePositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionSplice
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotInversionCounts

/-!
模型。文献の定義との比較は後で
# 二出現色への挿入の両向き交差逆転数

概要：Berger–Fresse §2.2.6 の合成活動列の逆転数を最初の指定出現との交差数で評価する。
方針：内側列の前後を分け、各交差対を元の一活動位置との対へ戻す。
規約：正の内側 arity と任意の内外語次数。
使われ方：二出現色分岐の一般係数等式。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

local notation "r₀" => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k (Fin.mk 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k))

/-- 概要：第一部分語へ送る内側二位置の逆転寄与は元と一致（BF §2.2.4・§2.2.6）。
方針：位置と色はそれぞれ共通の数だけずれることを使う。
規約：両内側位置が切断点以下。
使われ方：内側活動像の内部逆転数。 -/
lemma nonpivotInnerMap_inversionTerm (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k)
    (i j : Fin (n + e)) (hi : i ≤ q) (hj : j ≤ q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
      (a.nonpivotInnerMap q ha hp i) (a.nonpivotInnerMap q ha hp j) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm v.val i j := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, a.nonpivotInnerMap_value hn q ha hp i hi,
    a.nonpivotInnerMap_value hn q ha hp j hj, a.nonpivotInnerMap_lt_iff q ha hp i j hi hj,
    Fin.lt_def, _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition_val, Nat.add_lt_add_iff_left]

/-- 概要：内側各活動位置との両向き交差は元の最初の指定出現との対（BF §2.2.6）。
方針：外側位置が最初の指定出現の前か後かで位置順序と色順序を戻す。
規約：外側位置は最初の指定出現を除いた活動位置。
使われ方：内側活動数倍の一様交差項を得る。 -/
lemma nonpivot_cross_inversionTerm (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k)
    (r : Fin (m + 1 + d)) (hr : r ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase r₀)
    (j : Fin (n + e)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
        (a.remainingPositionMap r) (a.nonpivotInnerMap q ha hp j) +
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
        (a.nonpivotInnerMap q ha hp j) (a.remainingPositionMap r) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u.val r r₀ + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u.val r₀ r := by
  have H := a.property.2
  rw [ha] at H
  have hjq := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot H.2 hj
  have hrk := a.remaining_color_ne_of_nonpivot q ha hp r hr
  have hvr : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val (a.remainingPositionMap r) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨u.val r, hrk⟩ := by
    rw [a.remainingPositionMap_of_ne r hrk, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_outerPosition]
  have hvj := a.nonpivotInnerMap_value hn q ha hp j hjq
  have hv0 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k⟩
  rcases lt_or_gt_of_ne (Finset.mem_erase.mp hr).1 with h | h
  · have hmap := a.remainingPositionMap_lt_nonpivotInnerMap q ha hp r hrk h j hjq
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hmap, not_lt_of_ge hmap.le, h, not_lt_of_ge h.le,
      true_and, false_and, ite_false, Nat.add_zero, hv0, hvr, hvj,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertedPosition_lt_remaining_iff]
  · have hmap := a.nonpivotInnerMap_lt_remainingPositionMap q ha hp r hrk h j hjq
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hmap, not_lt_of_ge hmap.le, h, not_lt_of_ge h.le,
      true_and, false_and, ite_false, Nat.zero_add, hv0, hvr, hvj,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remainingPosition_lt_inserted_iff]

/-- 概要：二出現色分岐の全合成逆転数は内外逆転数と両向き交差数（BF §2.2.6）。
方針：合成活動集合の二像表示で内部対と交差対を添字変更する。
規約：外側の最初の指定出現を一つだけ除く。
使われ方：削除の順位釣り合いと合成指数へ接続する。 -/
lemma inversionCount_nonpivot (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase r₀) +
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q) +
          (e + 1) * ∑ r ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase r₀,
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u.val r r₀ + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u.val r₀ r) := by
  have Hq := a.property.2
  rw [ha] at Hq
  rw [← a.activePositions_nonpivot_union hn q ha hp]
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_splice_images u.val v.val
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase r₀) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q) r₀
    a.remainingPositionMap (a.nonpivotInnerMap q ha hp)
    (a.remainingPositionMap_nonpivot_injOn q ha hp) (a.nonpivotInnerMap_injOn q ha hp)
    (a.nonpivot_active_images_disjoint q ha hp)
    (fun r hr s hs => a.remainingPositionMap_inversionTerm_of_ne hn r s
      (a.remaining_color_ne_of_nonpivot q ha hp r hr)
      (a.remaining_color_ne_of_nonpivot q ha hp s hs))
    (fun i hi j hj => a.nonpivotInnerMap_inversionTerm hn q ha hp i j
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot Hq.2 hi) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot Hq.2 hj))
    (fun r hr j hj => a.nonpivot_cross_inversionTerm hn q ha hp r hr j hj)
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_card v q Hq.2] using H

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut
