module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositionCutPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeWordOccurrence

/-!
模型。文献の定義との比較は後で
# 重なる分割の各部分語の合成位置

概要：Berger–Fresse §2.2.6 の各挿入部分語の位置を実際の合成基底語へ送る。
方針：第 i 出現の前の代入済み接頭語長を加え、リスト分解で値と順序を照合する。
規約：一出現性を仮定せず全ての重なる分割を扱う。
使われ方：隣接部分語の共有端点の二出現から合成切断点の範囲を制限する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：元の接頭語を延ばすと代入済み接頭語長は減らない（BF §2.2.6）。
方針：短い接頭語を長い接頭語の先頭として切り、代入の連結則を使う。
規約：部分語不足や空部分語も許す。
使われ方：異なる挿入部分語の位置の順序。 -/
lemma substitute_prefix_length_mono {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n))) {a b : ℕ} (hab : a ≤ b) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (xs.take a) parts).length ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (xs.take b) parts).length := by
  have hs := List.take_append_drop a (xs.take b)
  rw [List.take_take, Nat.min_eq_left hab] at hs
  have H := congrArg (fun ys => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ys parts).length) hs
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_append, List.length_append] at H
  omega

/-- 概要：各部分語内の位置を合成語の有限位置へ送る（BF §2.2.6）。
方針：その指定出現の前の代入済み接頭語長に部分語内の位置を加える。
規約：空部分語には位置がなく、内側 arity 零でも定義可能。
使われ方：共有端点の二つの合成位置を構成する。 -/
def compositeSegmentPosition {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) (q : Fin (r.val i).val) :
    Fin (m + n + (d + e)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val)
      (r.segments v.val)).length + q.val, by
    have H := congrArg List.length (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_at_occurrence u v k r i)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length] at H
    simp only [List.length_append, List.length_map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment_length] at H
    have := q.isLt
    omega⟩

/-- 概要：各部分語位置の合成基底語での値は元の挿入ラベル（BF §2.2.6）。
方針：前置語長を差し引き、segment の drop・take を元位置で評価する。
規約：内側位置は部分語開始と相対位置の和。
使われ方：隣接した部分語の末尾と先頭の色の一致。 -/
lemma compositeSegmentPosition_value {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) (q : Fin (r.val i).val) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition u v k r i q) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k
        (v.val ⟨r.start i + q.val, by
          have := r.start_add_length_le i; have := q.isLt; omega⟩) := by
  have hq : q.val < ((r.segment v.val i).map
      (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k)).length := by
    simpa only [List.length_map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment_length] using q.isLt
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r)[(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition u v k r i q).val]'(by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length]; exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition u v k r i q).isLt) = _
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_at_occurrence u v k r i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition,
    List.append_assoc, List.getElem_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem_append_left hq, List.getElem_map]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment, List.getElem_take, List.getElem_drop, List.getElem_ofFn]

/-- 概要：指定出現を一文字越えると代入済み接頭語長は部分語長だけ増える（BF §2.2.6）。
方針：元の次の一文字を分け、消費済み部分語列の先頭を同じ segment と同定する。
規約：元の出現番号と部分語番号を一致させる。
使われ方：部分語全体が次の部分語より前に置かれること。 -/
lemma substitute_prefix_length_at_occurrence {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val + 1))
      (r.segments v.val)).length =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val)
      (r.segments v.val)).length + (r.val i).val := by
  have hl : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val < (List.ofFn u.val).length := by
    simpa only [List.length_ofFn] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).isLt
  rw [List.take_succ_eq_append_getElem hl, List.getElem_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k i,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_count_take u.val k i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute]
  simp only [List.append_nil, List.length_append, List.length_map,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segments, List.headD_eq_head?_getD, List.head?_eq_getElem?,
    List.getElem?_drop, Nat.add_zero, List.getElem?_ofFn, dite_eq_left i.isLt,
    Option.getD_some, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment_length]

/-- 概要：先の挿入部分語の全位置は後の部分語の全位置より前（BF §2.2.6）。
方針：前の出現直後の接頭語長を後の出現直前の長さで抑える。
規約：部分語の内部位置が存在する場合に述べる。
使われ方：共有端点の二出現が切断点を厳密に跨ぐこと。 -/
lemma compositeSegmentPosition_lt {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (i j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) (hij : i < j)
    (a : Fin (r.val i).val) (b : Fin (r.val j).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition u v k r i a < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition u v k r j b := by
  have ho := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono u.val k hij
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_mono k (List.ofFn u.val) (r.segments v.val)
    (show (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val + 1 ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j).val from ho)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_at_occurrence] at H
  change _ + a.val < _ + b.val
  have := a.isLt
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
