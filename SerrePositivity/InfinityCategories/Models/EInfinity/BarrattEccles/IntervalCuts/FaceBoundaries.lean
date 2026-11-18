module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.IntervalBoundary

/-!
模型。文献の定義との比較は後で
# 区間の三つの面生成元の境界

概要：Berger–Fresse §2.2.7 の出力境界を零・一・辺の三つの場合へ分ける。
方針：非空頂点集合を分類し、頂点は閉じ、辺の微分は二端点の差であることを使う。
規約：全て実際の正規化区間の整数生成元について述べる。
使われ方：テンソルの各因子の境界を頂点への置換へ変換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory

/-- 概要：区間の非退化単体は零頂点・一頂点・辺のいずれか（BF §2.2.1）。
方針：二頂点の所属で非空有限集合を分類する。
規約：向き付き辺は両頂点の集合。
使われ方：各出力単体の境界を三つの場合で検証する。 -/
lemma simplex_cases (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) : s = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 0 ∨ s = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 1 ∨ s = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge := by
  by_cases h0 : (0 : Fin 2) ∈ s.val
  · by_cases h1 : (1 : Fin 2) ∈ s.val
    · right; right
      apply Subtype.ext
      apply Finset.ext
      intro i
      fin_cases i <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge, h0, h1]
    · left
      apply Subtype.ext
      apply Finset.ext
      intro i
      fin_cases i <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex, h0, h1]
  · right; left
    have h1 : (1 : Fin 2) ∈ s.val := by
      obtain ⟨i, hi⟩ := s.property
      fin_cases i
      · exact False.elim (h0 hi)
      · exact hi
    apply Subtype.ext
    apply Finset.ext
    intro i
    fin_cases i <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex, h0, h1]

/-- 概要：頂点の単体次数は零（BF §2.2.3）。
方針：一元集合の濃度を計算する。
規約：両端点を含む。
使われ方：頂点因子の微分と Koszul 符号の簡約。 -/
@[simp] lemma simplexDegree_vertex (b : Fin 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex]

/-- 概要：辺の単体次数は一（BF §2.2.3）。
方針：二頂点の全体集合の濃度を計算する。
規約：鎖次数。
使われ方：辺因子の微分と Koszul 符号の簡約。 -/
@[simp] lemma simplexDegree_edge : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge = 1 := by decide

variable (A : Type u) [CommRing A]

/-- 概要：整数区間の頂点の微分は零（BF §2.2.7）。
方針：微分の終域である整数次数一が零対象であることを使う。
規約：零・一の両頂点。
使われ方：頂点因子のテンソル境界項を消去する。 -/
lemma faceVector_vertex_d (b : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d 0 1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) = 0 := by
  let _ := ModuleCat.isZero_iff_subsingleton.mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_isZero_positive A 1 (by decide))
  exact Subsingleton.elim _ _

/-- 概要：辺の微分を同じ面生成元の二端点の差で表す（BF §2.2.7）。
方針：正規化鎖での境界を整数表示へ移し、面と頂点生成元を同定する。
規約：整数次数 −1 から零。
使われ方：辺因子の境界項を終点・始点のテンソルの差へ展開する。 -/
lemma faceVector_edge_d_sub : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d (-1) 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) =
    (show (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0 from _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 1)) -
      (show (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0 from _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 0)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_edge_d, map_sub]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain_vertex]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
