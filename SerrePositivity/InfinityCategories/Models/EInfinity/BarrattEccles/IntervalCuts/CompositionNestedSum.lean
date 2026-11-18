module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedCutSurjective

/-!
模型。文献の定義との比較は後で
# 実際の部分合成の辺成分を二段切断で添字付けする

概要：Berger–Fresse §2.2.6 の合成辺成分の有限和を二段切断上の和へ移す。
方針：退化切断の零項を除き、非零合成切断との有限同値で添字変更する。
規約：正の内側 arity、任意の可換環、実際の符号付き面テンソルを保持する。
使われ方：部分合成則の右辺の全出力族と Koszul 符号を比較する共通の有限和。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：合成辺成分の二重和は非零合成切断上の全和（BF §2.2.6）。
方針：分割と位置の直積上の和へ直し、退化時の零項を部分型で除く。
規約：項は実際の合成符号・切断符号・出力テンソルを持つ。
使われ方：二段切断との有限同値による添字変更の直前の和。 -/
lemma edgeComponent_composition_nonzero_cut_sum {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1)) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A (m + n) (d + e) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A u v k) =
      ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositeEdgeCut u v k hn,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositionEdgeCutTerm A u v k c.val.1 hn c.val.2 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent_composition_cut_sum A u v k hn,
    ← Fintype.sum_prod_type (fun c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e) ×
      Fin (m + n + (d + e)) => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositionEdgeCutTerm A u v k c.1 hn c.2)]
  calc
    _ = ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositeEdgeCut u v k hn,
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign u v k c.val.1 *
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k c.val.1 hn).val c.val.2) •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A (m + n) (d + e + 1)
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k c.val.1 hn) c.val.2)
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ c.val.2 c.property) := by
      unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositionEdgeCutTerm
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_dite_eq_subtype _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositionEdgeCutTerm, dite_eq_left c.property]

/-- 概要：合成辺成分は二段切断上の実際の合成切断項の和（BF §2.2.6）。
方針：非零合成切断の和を構成済みの有限同値で添字変更する。
規約：右辺の値はまだ合成語の全出力・符号であり、二段作用の値との一致は別に照合する。
使われ方：部分合成則の両辺の項ごとの比較の左辺。 -/
lemma edgeComponent_composition_nested_cut_sum {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1)) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A (m + n) (d + e) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A u v k) =
      ∑ a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositionEdgeCutTerm A u v k a.partition hn a.compositePosition := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent_composition_nonzero_cut_sum A u v k hn]
  exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositeCutEquiv hn).sum_comp
    (fun c => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositionEdgeCutTerm A u v k c.val.1 hn c.val.2)).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
