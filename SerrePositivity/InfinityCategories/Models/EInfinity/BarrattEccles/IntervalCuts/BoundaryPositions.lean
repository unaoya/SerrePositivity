module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.OutputOccurrences
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorBoundaryValues

/-!
模型。文献の定義との比較は後で
# 切断のテンソル境界を元の活動位置で添字付ける

概要：Berger–Fresse §2.2.7 の境界の辺因子を元の語の区切りと切断点へ同定する。
方針：活動位置上の色の単射性と辺の出力の特徴付けで有限和を添字替えする。
規約：各符号と実際のテンソル境界項はそのまま保持する。
使われ方：辺の境界を語の一文字削除へ比較する最初の添字替え。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

/-- 概要：非零切断の辺出力色の集合は活動位置の色の像（BF §2.2.3）。
方針：各色で所属を比較し、辺の出力の特徴付けを使う。
規約：像は重複を持たず、切断点と全区切りを含む。
使われ方：境界の有限和の添字を色から元位置へ変える。 -/
lemma edgeOutput_edges_eq_image {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    Finset.univ.filter (fun k : Fin n => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p).image u.val := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u p h]

/-- 概要：辺の出力因子の有限和は活動位置の有限和（BF §2.2.7）。
方針：活動位置の色の像とその単射性によって有限和を移す。
規約：値は任意の可換加法モノイドでよい。
使われ方：符号付き境界項と削除項の比較に適用する。 -/
lemma sum_edgeOutput_edges {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) {M : Type*} [AddCommMonoid M] (F : Fin n → M) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge), F k =
      ∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p, F (u.val i) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_edges_eq_image u p h]
  exact Finset.sum_image (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_injOn h)

variable (A : Type u) [CommRing A]

/-- 概要：実際の切断テンソルの境界は元の活動位置の境界項の和（BF §2.2.7）。
方針：一般のテンソル境界を辺だけへ制限し、活動位置へ添字替えする。
規約：切断符号を掛ける前の、実際の区間テンソルの境界。
使われ方：各活動位置の二端点への展開を語の削除と比較する。 -/
lemma edgeOutput_tensorVector_d {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) : ℤ))
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p)) =
      ∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) (u.val i) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector_d_eq_sum_edges]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_edgeOutput_edges u p h _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
