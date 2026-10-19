module

public import SerrePositivity.EInfinity.IntervalCuts.InsertedMembership
public import SerrePositivity.EInfinity.IntervalCuts.NonSlotRemainingOutput
public import SerrePositivity.EInfinity.IntervalCuts.NestedCutValidity

/-!
# 二部分割の辺入力の挿入出力

概要：Berger–Fresse §2.2.6 の二出現色への挿入では内側切断の出力を保持する。
方針：外側指定色の左右一出現から、合成の左右が内側の第一・第二部分語だけを消費すると示す。
規約：外側切断点色と指定色は異なる。
使われ方：二段切断の非切断点色の辺入力分岐の全挿入出力族。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：非切断点色の辺出力は左右のリストに一回ずつ現れる（BF §2.2.3）。
方針：両出力頂点の所属と左右 Nodup で count を一へ定める。
規約：左は切断点以前と切断点自身までの両方を記録する。
使われ方：代入の左右が消費する部分語数を一に決める。 -/
lemma edge_slot_list_counts {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) (k : Fin n) (hp : u.val p ≠ k)
    (hk : edgeOutput u p k = edge) :
    ((List.ofFn u.val).take p.val).count k = 1 ∧
      ((List.ofFn u.val).take (p.val + 1)).count k = 1 ∧
      ((List.ofFn u.val).drop p.val).count k = 1 := by
  have hv : edgeOutputVertices u.val p k = Finset.univ := congrArg Subtype.val hk
  have hLmem : k ∈ (List.ofFn u.val).take (p.val + 1) := by
    apply (zero_mem_edgeOutputVertices_iff_mem_take u.val p k).mp
    rw [hv]
    exact Finset.mem_univ _
  have hRmem : k ∈ (List.ofFn u.val).drop p.val := by
    apply (one_mem_edgeOutputVertices_iff_mem_drop u.val p k).mp
    rw [hv]
    exact Finset.mem_univ _
  have hL := List.count_eq_one_of_mem (cut_prefix_nodup u.val p h) hLmem
  have hR := List.count_eq_one_of_mem (cut_suffix_nodup u.val p h) hRmem
  have hl : p.val < (List.ofFn u.val).length := by
    simpa only [List.length_ofFn] using p.isLt
  have hbefore := hL
  rw [List.take_succ_eq_append_getElem hl, List.getElem_ofFn, List.count_append] at hbefore
  simp only [List.count_cons_of_ne hp, List.count_nil, Nat.add_zero] at hbefore
  exact ⟨hbefore, hL, hR⟩

/-- 概要：標準二部分割の部分語列は共有位置までの接頭語と接尾語（BF §1.2.4）。
方針：二つの有限部分語を順に評価する。
規約：共有文字を両方に含める。
使われ方：合成の左右代入に渡す消費前後の部分語列。 -/
lemma two_partition_segments {n l : ℕ} (v : Fin l → Fin n) (q : Fin l) :
    (OverlapPartition.two q).segments v =
      [(List.ofFn v).take (q.val + 1), (List.ofFn v).drop q.val] := by
  change [(OverlapPartition.two q).segment v 0, (OverlapPartition.two q).segment v 1] = _
  rw [OverlapPartition.two_segment_zero, OverlapPartition.two_segment_one]

/-- 概要：二部分語代入の全挿入出力は内側共有位置の切断出力（BF §2.2.6）。
方針：左右の指定色 count が一なので第一・第二部分語だけに所属判定を戻す。
規約：分割の部分語列を標準二部分語として明示する。
使われ方：非切断点色の辺入力分岐の実際の合成出力。 -/
lemma compositeOuterPosition_two_inserted_output {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) (h : EdgeNondegenerate u.val p)
    (hk : edgeOutput u p k = edge) (q : Fin (n + e))
    (hr : r.segments v.val = [(List.ofFn v.val).take (q.val + 1), (List.ofFn v.val).drop q.val])
    (b : Fin n) :
    edgeOutput (compositeBasisWord u v k r hn) (compositeOuterPosition u v k r p hp)
      (BarrattEccles.insertedPosition m n k b) = edgeOutput v q b := by
  have H := edge_slot_list_counts u p h k hp hk
  apply Subtype.ext
  apply edgeOutputVertices_eq_of_list_membership
  · rw [compositeOuterPosition_prefix, inserted_mem_substitute_iff, H.2.1, hr]
    simp only [List.take_succ_cons, List.take_zero, List.flatten_cons,
      List.flatten_nil, List.append_nil]
  · rw [compositeOuterPosition_suffix, inserted_mem_substitute_iff, H.2.2, H.1, hr]
    simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
      List.flatten_cons, List.flatten_nil, List.append_nil]

namespace NestedEdgeCut

/-- 概要：二出現色の辺入力の二段切断では全挿入色の出力は内側出力（BF §2.2.6）。
方針：構成した分割を標準二部分語へ移し、左右一出現の代入公式を使う。
規約：外側切断点色が指定色と異なる場合。
使われ方：全二段切断の出力族比較の最後の挿入分岐。 -/
lemma compositePosition_nonpivot_inserted_output {m n d e : ℕ}
    {u : BasisWord (m + 1) d} {v : BasisWord n e} {k : Fin (m + 1)}
    (a : NestedEdgeCut u v k) (hn : 0 < n) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) (b : Fin n) :
    edgeOutput (compositeBasisWord u v k a.partition hn) a.compositePosition
      (BarrattEccles.insertedPosition m n k b) = edgeOutput v q b := by
  have hc := a.occurrenceCount_eq_two_of_some_nonpivot q ha (Ne.symm hp)
  have hs := segments_cast_count hc a.partition v.val
  rw [partition_of_some_nonpivot a q ha (Ne.symm hp), two_partition_segments] at hs
  have H := a.property.2
  rw [ha] at H
  rw [compositePosition_nonpivot_eq_outer a hp]
  exact compositeOuterPosition_two_inserted_output u v k a.partition hn a.val.1 hp
    a.property.1 H.1 q hs.symm b

end NestedEdgeCut

end SerrePositivity.EInfinity.IntervalCuts
