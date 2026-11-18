module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InsertedMembership
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonSlotRemainingOutput

/-!
模型。文献の定義との比較は後で
# 一部分割の頂点入力の挿入出力

概要：Berger–Fresse §2.2.6 の一出現挿入では全挿入色の出力は外側指定色の頂点と一致する。
方針：唯一部分語が内側全語を覆うことと全射性で、挿入色の所属を指定色の所属へ戻す。
規約：切断点は指定色以外の外側位置にある。
使われ方：二段作用の内側頂点入力分岐の全挿入出力族。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：内側全語一つへの代入で挿入色の所属は指定色の所属と同値（BF §2.2.6）。
方針：指定色が現れれば唯一の部分語を消費し、内側全射性から全色が現れる。
規約：外側リストの指定色の回数は制限しない。
使われ方：一部分割の左側の出力頂点の照合。 -/
lemma inserted_mem_substitute_single_iff {m n e : ℕ} (k : Fin (m + 1))
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (b : Fin n) (xs : List (Fin (m + 1))) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs [List.ofFn v.val] ↔ k ∈ xs := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.inserted_mem_substitute_iff]
  by_cases hk : k ∈ xs
  · have hc := List.count_pos_iff.mpr hk
    rw [List.take_of_length_le (by simp only [List.length_singleton]; omega),
      List.flatten_cons, List.flatten_nil, List.append_nil]
    exact iff_of_true (List.mem_ofFn.mpr (v.surjective b)) hk
  · simp only [List.count_eq_zero.mpr hk, List.take_zero, List.flatten_nil,
      List.not_mem_nil, hk]

/-- 概要：一出現を左右で消費した後も右代入の挿入色所属は指定色所属（BF §2.2.6）。
方針：左が未消費なら全語一つの公式を、既消費なら右に指定色がないことを使う。
規約：左右の指定色回数の和を一とする。
使われ方：一部分割の右側の出力頂点の照合。 -/
lemma inserted_mem_substitute_single_tail_iff {m n e : ℕ} (k : Fin (m + 1))
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (b : Fin n) (xs ys : List (Fin (m + 1)))
    (h : xs.count k + ys.count k = 1) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b ∈
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ys ([List.ofFn v.val].drop (xs.count k)) ↔ k ∈ ys := by
  by_cases hx : xs.count k = 0
  · rw [hx, List.drop_zero]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.inserted_mem_substitute_single_iff k v b ys
  · have hy : k ∉ ys := List.count_eq_zero.mp (by omega)
    exact iff_of_false (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.inserted_not_mem_substitute_of_no_slot k b ys _ hy) hy

/-- 概要：一出現挿入の外側切断点では全挿入出力は外側指定色の出力（BF §2.2.6）。
方針：合成の左右リストへの挿入色の所属を同じ外側指定色の所属に戻す。
規約：内側語次数への仮定は不要。
使われ方：非零二段切断では頂点出力への内側次数零の作用の値となる。 -/
lemma compositeOuterPosition_single_inserted_output {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) (p : Fin (m + 1 + d)) (hp : u.val p ≠ k)
    (b : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_eq_of_list_membership
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segments_of_count_one r hc]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.inserted_mem_substitute_single_iff k v b _
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_suffix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segments_of_count_one r hc]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.inserted_mem_substitute_single_tail_iff
    have H := congrArg (List.count k) (List.take_append_drop p.val (List.ofFn u.val))
    rw [List.count_append] at H
    exact H.trans hc

namespace NestedEdgeCut

/-- 概要：内側頂点入力分岐の全挿入色の出力は外側指定色の頂点（BF §2.2.6）。
方針：頂点入力の一出現性と合成位置の外側表示を使う。
規約：頂点が零か一かを区別せず同じ公式で扱う。
使われ方：二段作用の内側頂点入力の全出力成分の一致。 -/
lemma compositePosition_vertex_inserted_output {m n d e : ℕ}
    {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}
    (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n) (ha : a.val.2 = none) (b : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn) a.compositePosition
      (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1 k := by
  have H := a.property.2
  rw [ha] at H
  have hp := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_ne_edge_iff_single_nonpivot u a.val.1 a.property.1 k).mp H.1).1
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_eq_outer a (Ne.symm hp)]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_single_inserted_output u v k a.partition hn
    (a.occurrenceCount_eq_one_of_none ha) a.val.1 (Ne.symm hp) b

end NestedEdgeCut

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
