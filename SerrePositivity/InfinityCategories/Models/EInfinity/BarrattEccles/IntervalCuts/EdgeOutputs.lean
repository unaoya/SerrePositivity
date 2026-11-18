module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeCuts
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
模型。文献の定義との比較は後で
# 辺の切断の出力と全次数

概要：Berger–Fresse §2.2.1–3 の各色の出力単体とその次数を有限集合で表す。
方針：展開位置の色の fiber を取り、零・一の頂点へ写して正規化する。
規約：全射語では各色の出力は非空。非退化項だけで元の頂点数を保つ。
使われ方：Δ¹ のテンソル基底への切断作用とその次数の型付け。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：辺の切断で指定した色へ集める全位置（BF §2.2.1）。
方針：展開位置を色で絞る。
規約：切断点の複製された両端を含む。
使われ方：各出力単体の頂点と次数。 -/
def edgeFiber {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) (k : Fin n) :
    Finset (Fin (l + 1)) := Finset.univ.filter (fun q => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeLabel u p q = k)

/-- 概要：指定した色の出力に現れる零・一の頂点（BF §2.2.1）。
方針：その色の全位置から頂点値の像を取る。
規約：退化項でも定義できるが重複は集合で忘れる。
使われ方：非退化項の正規化単体の指定。 -/
def edgeOutputVertices {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) (k : Fin n) :
    Finset (Fin 2) := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeFiber u p k).image (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeVertex p)

/-- 概要：全射語の辺の切断では各色が出現する（BF §2.2.1）。
方針：元の出現位置を切断点の左右に応じて展開位置へ持ち上げる。
規約：切断点自身は零頂点の側を選ぶ。
使われ方：出力を空単体とせず、零・一・辺のいずれかとする。 -/
lemma edgeFiber_nonempty {n l : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (p : Fin l) (k : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeFiber u.val p k).Nonempty := by
  obtain ⟨i, hi⟩ := u.surjective k
  by_cases hip : i ≤ p
  · refine ⟨i.castSucc, ?_⟩
    change i.castSucc ∈ Finset.univ.filter (fun q => u.val (p.predAbove q) = k)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [Fin.predAbove_castSucc_of_le _ _ hip, hi]⟩
  · refine ⟨i.succ, ?_⟩
    change i.succ ∈ Finset.univ.filter (fun q => u.val (p.predAbove q) = k)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [Fin.predAbove_succ_of_le _ _ (le_of_lt (lt_of_not_ge hip)), hi]⟩

/-- 概要：全射語では各出力の頂点集合も非空（BF §2.2.1）。
方針：非空な fiber の像を取る。
規約：arity 零では各色についての条件は空。
使われ方：頂点数−1 を単体の次数として計算する。 -/
lemma edgeOutputVertices_nonempty {n l : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (p : Fin l) (k : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u.val p k).Nonempty :=
  Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeFiber_nonempty u p k) _

/-- 概要：非退化な切断は各色の fiber の頂点数を保つ（BF §2.2.1）。
方針：同じ色で頂点値が一致すれば、色と頂点の対の単射性を使う。
規約：全射性は不要。
使われ方：全出力の次数和を入力の次数へ同定する。 -/
lemma edgeOutputVertices_card {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (k : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u p k).card = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeFiber u p k).card := by
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  have hi' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeLabel u p i = k := (Finset.mem_filter.mp hi).2
  have hj' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeLabel u p j = k := (Finset.mem_filter.mp hj).2
  apply h
  exact Prod.ext (hi'.trans hj'.symm) hij

/-- 概要：指定した色の出力単体の鎖次数（BF §2.2.3）。
方針：頂点集合の濃度から一を引く。
規約：非退化な切断で実際の単体次数となり、零または一。
使われ方：テンソル基底の総次数。 -/
def edgeOutputDegree {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) (k : Fin n) : ℕ :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u p k).card - 1

/-- 概要：辺の切断の全出力次数は d+1（BF §2.2.3）。
方針：全位置を色の fiber に分け、各非空 fiber の頂点数−1 を足す。
規約：入力語の次数は d、入力単体の次数は一。
使われ方：χ(d) と区間の辺から次数 d+1 のテンソルへの作用。 -/
lemma sum_edgeOutputDegree {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    ∑ k : Fin n, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputDegree u.val p k = d + 1 := by
  have hf : ∑ k : Fin n, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeFiber u.val p k).card = n + d + 1 := by
    simpa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeFiber] using
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin (n + d + 1))) Finset.univ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeLabel u.val p)
  have hk (k : Fin n) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeFiber u.val p k).card = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputDegree u.val p k + 1 := by
    have hp := Finset.card_pos.mpr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_nonempty u p k)
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_card h k]
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputDegree
    omega
  simp_rw [hk] at hf
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hf
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
