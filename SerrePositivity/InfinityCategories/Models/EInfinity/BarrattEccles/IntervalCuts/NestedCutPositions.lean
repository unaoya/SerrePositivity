module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedCuts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SingleSlotCut

/-!
模型。文献の定義との比較は後で
# 二段切断に対応する合成語の有限位置

概要：Berger–Fresse §2.2.6 の二段切断の全分岐から実際の合成語の切断点を構成する。
方針：切断点色への挿入では内側位置、他の色への挿入では外側位置を使う。
規約：合成分割は NestedEdgeCut.partition の構成に固定する。
使われ方：二段切断と合成切断の有限対応の順方向の位置成分。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一出現挿入の実際の合成基底語の内側位置の文字（BF §2.2.6）。
方針：有限基底語の評価を同じ合成リストの評価へ戻す。
規約：正の内側 arity を基底語の非退化性に使う。
使われ方：二段切断の切断点色を内側の挿入ラベルへ同定する。 -/
lemma compositeBasisWord_innerPosition {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1)
    (p : Fin (m + 1 + d)) (hp : u.val p = k) (q : Fin (n + e)) (hn : 0 < n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k (v.val q) := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition_value u v k r hc p hp q

namespace NestedEdgeCut

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

/-- 概要：二段切断の実際の合成語における有限切断点（BF §2.2.6）。
方針：辺入力で切断点色と一致するときだけ内側位置へ切り替える。
規約：頂点入力と他の辺入力では元の外側切断点を保持する。
使われ方：分割と合成位置の対への順方向写像。 -/
def compositePosition (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) : Fin (m + n + (d + e)) :=
  match ha : a.val.2 with
  | none => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k a.partition a.val.1 (by
      have H := a.property.2
      rw [ha] at H
      exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_ne_edge_iff_single_nonpivot u a.val.1 a.property.1 k).mp H.1).1.symm)
  | some q =>
    if hp : u.val a.val.1 = k then
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k a.partition (by
        rw [← hp]
        exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrenceCount_pivot_eq_one u a.val.1 a.property.1) a.val.1 hp q
    else _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k a.partition a.val.1 hp

/-- 概要：指定色以外の外側切断点では合成位置の文字は残りラベル（BF §2.2.6）。
方針：内側切断点の有無で分けて外側位置の評価を使う。
規約：正の内側 arity の実際の合成基底語。
使われ方：非切断点色分岐の切断点ラベルの一致。 -/
lemma compositePosition_nonpivot_value (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (hp : u.val a.val.1 ≠ k) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition =
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨u.val a.val.1, hp⟩ := by
  rcases a with ⟨⟨p, q⟩, h⟩
  cases q with
  | none => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_outerPosition _ _ _ _ hn _ _
  | some q =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition, dite_eq_right hp]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_outerPosition _ _ _ _ hn _ hp

/-- 概要：切断点色への内側辺作用では合成位置の文字は内側切断点の挿入ラベル（BF §2.2.6）。
方針：実際の内側位置の評価と二段切断の位置の構成を比較する。
規約：内側切断点を some として保持する。
使われ方：切断点色分岐の全出力族の比較の基点。 -/
lemma compositePosition_pivot_value (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 = k) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k (v.val q) := by
  rcases a with ⟨⟨p, s⟩, h⟩
  cases s with
  | none => cases ha
  | some s =>
    cases ha
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition, dite_eq_left hp]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_innerPosition _ _ _ _ _ _ hp _ hn

/-- 概要：切断点色への内側辺作用から選んだ合成位置は実際に非退化（BF §2.2.6）。
方針：一出現挿入の非退化性の一般公式を構成済みの分割と位置へ適用する。
規約：内側辺切断の非退化性は二段切断のデータが供給する。
使われ方：順方向写像の切断点色分岐を非零合成切断へ持ち上げる。 -/
lemma compositePosition_pivot_nondegenerate (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 = k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition := by
  rcases a with ⟨⟨p, s⟩, h⟩
  cases s with
  | none => cases ha
  | some s =>
    cases ha
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition, dite_eq_left hp]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.composite_single_slot_cut_nondegenerate _ _ _ _ _ _ hp h.1 _ h.2.2 hn

end NestedEdgeCut

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
