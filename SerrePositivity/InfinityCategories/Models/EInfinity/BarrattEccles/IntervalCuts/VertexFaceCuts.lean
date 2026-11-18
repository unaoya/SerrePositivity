module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCuts

/-!
模型。文献の定義との比較は後で
# 頂点入力の面切断と一定出力族

概要：Berger–Fresse §2.2.6 の非辺入力の面切断の出力・係数と一定族の代入を評価する。
方針：辺切断点 some を排除して唯一の none を使う。
規約：内側 arity 零も含む。
使われ方：実際の二段余作用の頂点入力を零か一定頂点族へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：頂点面は辺面と異なる（BF §2.2.1）。
方針：面次数零と一の不一致を使う。
規約：両頂点。
使われ方：頂点入力の面切断の辺分岐を排除する。 -/
lemma vertex_not_edge (b : Fin 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge := by
  intro he
  have H := congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree he
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_edge] at H
  exact Nat.zero_ne_one H

namespace FaceCut

/-- 概要：非辺入力の面切断は none だけ（BF §2.2.6）。
方針：some の入力辺条件を排除する。
規約：非辺入力で実際に存在する面切断を指定する。
使われ方：頂点入力の係数と出力族を一定値へ戻す。 -/
lemma val_eq_none_of_nonedge {n e : ℕ} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex}
    (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v s) (hs : s ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) : a.val = none := by
  have H := a.property
  cases ha : a.val with
  | none => rfl
  | some q => rw [ha] at H; exact False.elim (hs H.1)

/-- 概要：非辺入力の全出力族は同じ面の一定族（BF §2.2.6）。
方針：切断点 none の出力定義を評価する。
規約：出力 arity 零を含む。
使われ方：頂点余作用の出力テンソルの全因子。 -/
lemma output_of_nonedge {n e : ℕ} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex}
    (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v s) (hs : s ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) : a.output = fun _ => s := by
  funext j
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut.output, a.val_eq_none_of_nonedge hs]

/-- 概要：非辺入力の面切断係数は一（BF §2.2.6）。
方針：切断点 none の係数定義を評価する。
規約：係数は整数。
使われ方：頂点入力の一項の係数を消す。 -/
lemma coefficient_of_nonedge {n e : ℕ} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex}
    (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v s) (hs : s ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) : a.coefficient = 1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut.coefficient, a.val_eq_none_of_nonedge hs]

/-- 概要：次数零の頂点入力には面切断が一つだけ（BF §2.2.6）。
方針：既存の一元型との同値の濃度を比較する。
規約：両頂点と arity 零。
使われ方：実際の内側余代入の有限和を一項へ戻す。 -/
lemma card_vertex {n : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0) (b : Fin 2) :
    Fintype.card (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) = 1 := by
  simpa using Fintype.card_congr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut.vertexEquiv v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_not_edge b) rfl)

end FaceCut

/-- 概要：同じ一定族への同じ一定族の代入は同じ一定族（BF §3.1）。
方針：残りラベルと挿入ラベルの両定義を評価する。
規約：内側 arity 零も含む。
使われ方：二段頂点作用の全出力族を揃える。 -/
lemma insertionFamily_const {α : Type*} {m n : ℕ} (x : α) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily (fun _ : Fin (m + 1) => x) (fun _ : Fin n => x) i = fun _ => x := by
  funext j
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily
  cases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i j <;> rfl

/-- 概要：一定頂点族の全前方次数は零（BF §2.2.3）。
方針：各頂点の次数零を有限和へ代入する。
規約：前方因子数は任意。
使われ方：頂点余代入の Koszul 交換符号を消す。 -/
lemma prefixDegree_vertex (n : ℕ) (b : Fin 2) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree n (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) i = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex, Finset.sum_const_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
