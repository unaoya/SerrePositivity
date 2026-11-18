module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedOutputs
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositionNestedSum

/-!
模型。文献の定義との比較は後で
# 二段出力族による実際の合成辺成分の表示

概要：Berger–Fresse §2.2.6 の合成辺成分を二段出力族の面テンソルの和として表示する。
方針：全出力族の一致から全次数とテンソル値を移し、既存の有限和を項ごとに書き換える。
規約：符号はまだ元の合成符号と合成切断符号の積を保持する。
使われ方：二段作用の Koszul 符号との比較を係数の等式へ絞る。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.TensorPowers

namespace NestedEdgeCut

/-- 概要：二段切断の出力族の全次数は両語次数と入力辺次数の和（BF §2.2.3）。
方針：実際の非零合成切断の出力族の全次数へ戻す。
規約：全次数は自然数 d+e+1。
使われ方：実際の面テンソルの値域を合成辺成分と一致させる。 -/
lemma outputFamily_tupleDegree {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d}
    {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)} (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (m + n) a.outputFamily = d + e + 1 := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_outputFamily a hn]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ (a.compositePosition_nondegenerate hn)

/-- 概要：実際の合成切断項は二段出力族の面テンソルに同じ係数を掛けた値（BF §2.2.6）。
方針：非零性で条件分岐を評価し、全出力族の等式を実際のテンソルへ送る。
規約：元の合成符号と切断符号を保持する。
使われ方：部分合成則の符号を除く項の値の照合。 -/
lemma compositionEdgeCutTerm_outputFamily (A : Type u) [CommRing A]
    {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}
    (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositionEdgeCutTerm A u v k a.partition hn a.compositePosition =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign u v k a.partition *
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition) •
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A (m + n) (d + e + 1) a.outputFamily
          (a.outputFamily_tupleDegree hn) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositionEdgeCutTerm, dite_eq_left (a.compositePosition_nondegenerate hn),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_outputFamily]

end NestedEdgeCut

/-- 概要：実際の合成辺成分は二段出力族の符号付き面テンソル和（BF §2.2.6）。
方針：二段切断で添字付けた実際の合成項を出力族の一致で書き換える。
規約：係数は合成符号と合成切断符号の積で、二段作用の係数との一致は別工程。
使われ方：部分合成則の左辺を右辺と同じ出力基底族にそろえる。 -/
lemma edgeComponent_composition_nested_output_sum (A : Type u) [CommRing A]
    {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A (m + n) (d + e) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A u v k) =
      ∑ a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k,
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign u v k a.partition *
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition) •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A (m + n) (d + e + 1) a.outputFamily
            (a.outputFamily_tupleDegree hn) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent_composition_nested_cut_sum A u v k hn]
  apply Finset.sum_congr rfl
  intro a _
  exact a.compositionEdgeCutTerm_outputFamily A hn

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
