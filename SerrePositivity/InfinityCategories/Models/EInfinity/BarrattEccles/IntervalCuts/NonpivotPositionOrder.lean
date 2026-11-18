module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotFirstSegment

/-!
模型。文献の定義との比較は後で
# 二出現色への内側活動列と前後の残り位置

概要：Berger–Fresse §2.2.6 の内側活動列は最初の指定出現の前後の残り位置の間に入る。
方針：第一部分語の前後の接頭語長で内側位置を挟む。
規約：内側切断点以下の位置だけを比較する。
使われ方：二出現色分岐の両向きの交差逆転数。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：残り色が挿入色より小さい条件は元の残り色が指定色より小さいこと（BF §2.2.6）。
方針：挿入色の範囲と残り色の番号公式を比較する。
規約：内側色の番号には依存しない。
使われ方：内側列から後方残り位置への交差逆転条件。 -/
lemma remainingPosition_lt_inserted_iff {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (c : {c : Fin (m + 1) // c ≠ k}) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k c < _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b ↔
      c.val < k := by
  simp only [Fin.lt_def, _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition_val,
    _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_val, _root_.SerrePositivity.EInfinity.BarrattEccles.remainingValue]
  have hck : c.val.val ≠ k.val := fun h => c.property (Fin.ext h)
  have := b.isLt
  split_ifs <;> omega

namespace NestedEdgeCut

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

local notation "r₀" => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k (Fin.mk 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k))

/-- 概要：最初の指定出現以外の外側活動位置は指定色と異なる（BF §2.2.3）。
方針：活動色の単射性と最初の指定出現の活動性を使う。
規約：内側辺作用の二出現分岐。
使われ方：外側残り活動像の位置写像と色写像を評価する。 -/
lemma remaining_color_ne_of_nonpivot (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) (r : Fin (m + 1 + d))
    (hr : r ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase r₀) : u.val r ≠ k := by
  intro he
  have hr' := Finset.mem_erase.mp hr
  exact hr'.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_injOn a.property.1 hr'.2 (a.nonpivot_first_mem_active q ha hp)
    (he.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k⟩).symm))

/-- 概要：最初の指定出現より前の残り位置は全内側活動位置より前（BF §2.2.6）。
方針：残り位置を一文字越えた接頭語長を第一部分語の前置長で抑える。
規約：内側の指定位置が切断点以下であることを要求する。
使われ方：前方残り位置と内側列の交差対。 -/
lemma remainingPositionMap_lt_nonpivotInnerMap (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) (r : Fin (m + 1 + d))
    (hr : u.val r ≠ k) (horder : r < r₀) (j : Fin (n + e)) (hj : j ≤ q) :
    a.remainingPositionMap r < a.nonpivotInnerMap q ha hp j := by
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_mono k (List.ofFn u.val) (a.partition.segments v.val)
    (show r.val + 1 ≤ (r₀).val from horder)
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_at_non_slot k (List.ofFn u.val)
    (a.partition.segments v.val) ⟨r.val, by simpa only [List.length_ofFn] using r.isLt⟩
      (by simpa only [List.getElem_ofFn] using hr)
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take (r.val + 1))
      (a.partition.segments v.val)).length =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take r.val) (a.partition.segments v.val)).length + 1 at hs
  rw [hs] at H
  change (a.remainingPositionMap r).val < (a.nonpivotInnerMap q ha hp j).val
  rw [a.remainingPositionMap_of_ne r hr, a.nonpivotInnerMap_val q ha hp j hj]
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take r.val) (a.partition.segments v.val)).length < _
  omega

/-- 概要：全内側活動位置は最初の指定出現より後の残り位置より前（BF §2.2.6）。
方針：第一部分語を全て通過した接頭語長を後方位置の前置長で抑える。
規約：第二指定出現ではなく指定色以外の位置を比較する。
使われ方：内側列と後方残り位置の交差対。 -/
lemma nonpivotInnerMap_lt_remainingPositionMap (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) (r : Fin (m + 1 + d))
    (hr : u.val r ≠ k) (horder : r₀ < r) (j : Fin (n + e)) (hj : j ≤ q) :
    a.nonpivotInnerMap q ha hp j < a.remainingPositionMap r := by
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_mono k (List.ofFn u.val) (a.partition.segments v.val)
    (show (r₀).val + 1 ≤ r.val from horder)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_at_occurrence u v k a.partition
    ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k⟩, a.nonpivot_first_length q ha hp] at H
  change (a.nonpivotInnerMap q ha hp j).val < (a.remainingPositionMap r).val
  rw [a.nonpivotInnerMap_val q ha hp j hj, a.remainingPositionMap_of_ne r hr]
  change _ < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take r.val) (a.partition.segments v.val)).length
  omega

end NestedEdgeCut

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
