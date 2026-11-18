module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotInsertedOutput
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SingleBlockInsertedOutput
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TwoBlockInsertedOutput

/-!
模型。文献の定義との比較は後で
# 二段切断と合成切断の全出力族の一致

概要：Berger–Fresse §2.2.6 の部分合成の対応する切断は全出力単体族が一致する。
方針：残り色では外側の出力、挿入色では内側の辺出力または指定された頂点を使う。
規約：正の内側 arity、全外側・内側次数と全分岐を含む。
使われ方：実際の合成辺成分と二段作用の面テンソル値の照合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：全二段切断で挿入色の出力は内側入力の種類で決まる（BF §2.2.6）。
方針：頂点入力と辺入力を分け、辺入力は外側切断点色の一致・不一致をさらに分ける。
規約：none では外側指定色の頂点、some q では内側切断 q の出力。
使われ方：全出力族の挿入色成分の一般式。 -/
lemma compositePosition_inserted_output {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d}
    {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)} (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (b : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn) a.compositePosition
      (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b) =
      match a.val.2 with
      | none => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1 k
      | some q => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput v q b := by
  cases ha : a.val.2 with
  | none => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_vertex_inserted_output a hn ha b
  | some q =>
    by_cases hp : u.val a.val.1 = k
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_pivot_inserted_output a hn q ha hp b
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_inserted_output a hn q ha hp b

/-- 概要：二段切断の出力単体族（BF §2.2.6）。
方針：合成の入力分解で、残り色に外側出力、挿入色に頂点または内側出力を割り当てる。
規約：入力ラベルは実際の部分合成と同じ順序。
使われ方：部分合成則の右辺のテンソル基底族。 -/
def outputFamily {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e}
    {k : Fin (m + 1)} (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (j : Fin (m + n)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex :=
  match _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k j with
  | Sum.inl b => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1 b.val
  | Sum.inr b =>
    match a.val.2 with
    | none => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1 k
    | some q => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput v q b

/-- 概要：対応する実際の合成切断の全出力族は二段切断の出力族に一致（BF §2.2.6）。
方針：全入力ラベルを残り・挿入に分け、各成分の出力公式を使う。
規約：色ごとの式を関数全体の等式として束ねる。
使われ方：符号の照合後に実際の面テンソルの値を同定する。 -/
lemma compositePosition_outputFamily {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d}
    {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)} (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn) a.compositePosition =
      a.outputFamily := by
  funext j
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.outputFamily
  cases hj : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k j with
  | inl b =>
    have he : j = _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k b := by
      have H := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm hj
      simpa only [Equiv.symm_apply_apply, _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition] using H
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_remaining_output a hn b
  | inr b =>
    have he : j = _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b := by
      have H := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm hj
      simpa only [Equiv.symm_apply_apply, _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition] using H
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_inserted_output a hn b

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut
