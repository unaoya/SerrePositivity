module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SingleSlotOutputLists
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonSlotRemainingOutput
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedCutInjective

/-!
模型。文献の定義との比較は後で
# 全二段切断の残り色の出力族

概要：Berger–Fresse §2.2.6 の全二段切断で残り色の出力は外側切断の出力と一致する。
方針：切断点色への一出現挿入では左右の内側ブロックに残り色がないことを使う。
規約：内側頂点入力・辺入力、指定色と切断点色の一致・不一致を全て含む。
使われ方：部分合成則の全出力族の残り色成分の照合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一出現挿入の内側切断でも全残り色の出力は外側と一致（BF §2.2.6）。
方針：合成の左右を分解し、挿入ブロックには残り色がないことを使う。
規約：内側切断点は任意で、非零性を追加しない。
使われ方：切断点色分岐の残り出力の一致。 -/
lemma compositeInnerPosition_remaining_output {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) (p : Fin (m + 1 + d)) (hp : u.val p = k)
    (q : Fin (n + e)) (a : {a : Fin (m + 1) // a ≠ k}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p a.val := by
  have hl : p.val < (List.ofFn u.val).length := by
    simpa only [List.length_ofFn] using p.isLt
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_eq_of_list_membership
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition_prefix]
    simp only [List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remaining_not_mem_inserted_map, or_false,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remaining_mem_substitute_iff]
    rw [List.take_succ_eq_append_getElem hl, List.getElem_ofFn, hp]
    simp only [List.mem_append, List.mem_singleton, a.property, or_false]
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition_suffix]
    simp only [List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remaining_not_mem_inserted_map, false_or,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remaining_mem_substitute_iff]
    rw [List.drop_eq_getElem_cons hl, List.getElem_ofFn, hp]
    simp only [List.mem_cons, a.property, false_or]

namespace NestedEdgeCut

/-- 概要：切断点色分岐の合成位置は対応する内側位置（BF §2.2.6）。
方針：内側辺切断点と色の一致で位置の定義を評価する。
規約：一出現性の証明項は任意に指定できる。
使われ方：一出現挿入の出力公式への接続。 -/
lemma compositePosition_pivot_eq_inner {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d}
    {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)} (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 = k)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) :
    a.compositePosition = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k a.partition hc a.val.1 hp q := by
  rcases a with ⟨⟨p, s⟩, h⟩
  cases s with
  | none => cases ha
  | some s =>
    cases ha
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition, dite_eq_left hp]

/-- 概要：全二段切断で合成語の全残り色の出力は外側の出力（BF §2.2.6）。
方針：指定色と外側切断点色の一致を分け、それぞれの左右リスト比較を使う。
規約：正の内側 arity、全外側・内側次数、頂点・辺入力の両方。
使われ方：部分合成則の右辺の残り出力族との一般の一致。 -/
lemma compositePosition_remaining_output {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d}
    {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)} (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (b : {b : Fin (m + 1) // b ≠ k}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn) a.compositePosition
      (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1 b.val := by
  by_cases hp : u.val a.val.1 = k
  · obtain ⟨q, hq⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.exists_some_of_pivot a hp
    have hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1 := by
      rw [← hp]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrenceCount_pivot_eq_one u a.val.1 a.property.1
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_pivot_eq_inner a q hq hp hc]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition_remaining_output u v k a.partition hn hc a.val.1 hp q b
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_remaining_output a hn hp b

end NestedEdgeCut

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
