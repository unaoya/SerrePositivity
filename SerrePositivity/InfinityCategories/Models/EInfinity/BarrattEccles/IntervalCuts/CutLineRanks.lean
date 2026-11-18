module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ActiveSigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.LineRanks

/-!
模型。文献の定義との比較は後で
# 非零切断点以後の全射語の行番号

概要：Berger–Fresse §2.2.6 の非零切断では全区切りが切断点より前にある。
方針：行番号の区切り集合を全区切り集合と同定して語次数を得る。
規約：自然数の上界は語長を超えてもよい。
使われ方：非零切断での部分合成の Koszul 指数の簡約。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非零切断点以後の行番号は語次数（BF §1.2.5・§2.2.6）。
方針：全区切りが切断点より前なので上界条件を除く。
規約：切断点の行番号も含める。
使われ方：内側切断の前半・後半の成分次数を決める。 -/
lemma lineRank_after_pivot_eq_degree {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) (a : ℕ) (ha : p.val ≤ a) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank u.val a = d := by
  have hf : Finset.univ.filter (fun j : Fin (n + d) => j.val < a ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val j) =
      Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val) := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro hj
      have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_pivot h hj
      exact ⟨by change j.val < p.val at H; omega, hj⟩
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank, hf]
  simpa only [Fintype.card_subtype] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.card_caesuras_basisWord u

/-- 概要：非零切断点の区切り順位は語次数（BF §1.2.5・§2.2.6）。
方針：切断点の行番号を既存の区切り順位として読む。
規約：切断点自身は区切りではない。
使われ方：切断点色への一出現挿入の合成符号が正であること。 -/
lemma caesuraRank_pivot_eq_degree {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u.val p = d :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lineRank_after_pivot_eq_degree u p h p.val le_rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
