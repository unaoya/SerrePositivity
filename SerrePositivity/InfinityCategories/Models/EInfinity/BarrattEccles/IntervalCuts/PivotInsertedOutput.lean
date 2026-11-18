module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InsertedMembership
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RemainingOutputs

/-!
模型。文献の定義との比較は後で
# 切断点色への挿入の内側出力

概要：Berger–Fresse §2.2.6 の一出現挿入の挿入色出力は内側切断の出力と一致する。
方針：左右の外側ブロックに挿入色がないことを使い、同じ内側左右リストへ戻す。
規約：正の内側 arity、内側切断点は任意。
使われ方：二段切断の切断点色分岐の全挿入出力族。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一出現挿入の内側切断では挿入色の出力は内側切断の出力（BF §2.2.6）。
方針：左右のリストを三ブロック分解し、前後の指定色不出現と挿入ラベルの単射性を使う。
規約：切断の非零性を追加しない。
使われ方：部分合成の切断点色分岐の全挿入出力の照合。 -/
lemma compositeInnerPosition_inserted_output {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) (p : Fin (m + 1 + d)) (hp : u.val p = k)
    (q : Fin (n + e)) (b : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput v q b := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_eq_of_list_membership
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition_prefix]
    simp only [List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.inserted_not_mem_substitute_of_no_slot k b _ _
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.single_slot_not_mem_prefix u.val k hc p hp), false_or,
      List.mem_map_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m n k)]
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition_suffix]
    simp only [List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.inserted_not_mem_substitute_of_no_slot k b _ _
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.single_slot_not_mem_suffix u.val k hc p hp), or_false,
      List.mem_map_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m n k)]

namespace NestedEdgeCut

/-- 概要：切断点色分岐の二段切断の全挿入色出力は内側切断の出力（BF §2.2.6）。
方針：一出現性と実際の内側切断位置の式へ戻す。
規約：外側切断点色が指定色と一致する場合。
使われ方：二段作用の右辺の全出力族の挿入成分。 -/
lemma compositePosition_pivot_inserted_output {m n d e : ℕ}
    {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}
    (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 = k) (b : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn) a.compositePosition
      (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput v q b := by
  have hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1 := by
    rw [← hp]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrenceCount_pivot_eq_one u a.val.1 a.property.1
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_pivot_eq_inner a q ha hp hc]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition_inserted_output u v k a.partition hn hc a.val.1 hp q b

end NestedEdgeCut

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
