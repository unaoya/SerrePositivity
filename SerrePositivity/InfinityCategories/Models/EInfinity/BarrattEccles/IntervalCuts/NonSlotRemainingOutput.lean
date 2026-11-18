module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.OutputListMembership
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonSlotCut
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedCutPositions

/-!
模型。文献の定義との比較は後で
# 外側切断点を保持する代入の残り出力

概要：Berger–Fresse §2.2.6 の非切断点色への代入は全ての残り色の出力単体を保つ。
方針：合成切断の左右リストへの代入と残りラベルの所属の同値を使う。
規約：全射語次数・重なる分割は任意で、切断の非零性を追加しない。
使われ方：二段切断の全出力族の残り色成分。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：外側切断点を保つ代入は指定色以外の出力単体を保持（BF §2.2.6）。
方針：左右の出力頂点の所属を同じ外側語の左右の所属へ戻す。
規約：正の内側 arity、任意の分割・外側切断位置。
使われ方：一部分割・二部分割の全残り色の出力照合。 -/
lemma compositeOuterPosition_remaining_output {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k)
    (a : {a : Fin (m + 1) // a ≠ k}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p a.val := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_eq_of_list_membership
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_prefix]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remaining_mem_substitute_iff k a _ _
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_suffix]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remaining_mem_substitute_iff k a _ _

namespace NestedEdgeCut

/-- 概要：非切断点色分岐の合成位置は元の外側位置に一致（BF §2.2.6）。
方針：内側辺切断点の有無で場合分けして位置の定義を評価する。
規約：内側 arity の正性は不要。
使われ方：実際の二段切断の出力を外側位置の出力公式へ接続する。 -/
lemma compositePosition_nonpivot_eq_outer {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d}
    {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)} (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (hp : u.val a.val.1 ≠ k) :
    a.compositePosition = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k a.partition a.val.1 hp := by
  rcases a with ⟨⟨p, s⟩, h⟩
  cases s with
  | none => rfl
  | some s => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition, dite_eq_right hp]

/-- 概要：非切断点色分岐の二段切断は全残り色の出力単体を保持（BF §2.2.6）。
方針：合成位置の外側表示と残りラベルの出力公式を使う。
規約：内側頂点入力・辺入力を同時に扱う。
使われ方：右辺の出力族との成分ごとの一致。 -/
lemma compositePosition_nonpivot_remaining_output {m n d e : ℕ}
    {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}
    (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n) (hp : u.val a.val.1 ≠ k)
    (b : {b : Fin (m + 1) // b ≠ k}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn) a.compositePosition
      (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1 b.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_eq_outer a hp]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_remaining_output u v k a.partition hn a.val.1 hp b

end NestedEdgeCut

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
