module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorBoundaryTerms
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceBoundaries

/-!
模型。文献の定義との比較は後で
# 区間テンソルの境界の頂点と辺での値

概要：Berger–Fresse §2.2.7 のテンソル境界の各項を区間の三つの面で整理する。
方針：頂点因子の微分を消し、辺因子の微分を終点−始点として展開する。
規約：境界項は実際の反復テンソルの同じ次数成分に置く。
使われ方：全射語の削除から来る各切断項との符号付き比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：頂点と等しい面の整数境界は零（BF §2.2.7）。
方針：面を頂点へ置き換えて次数零の境界を使う。
規約：微分の次数を面の次数で指定する。
使われ方：因子ごとの境界項の零性に適用する。 -/
lemma faceVector_d_eq_zero_of_vertex (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (b : Fin 2) (hs : s = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ) + 1)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A s) = 0 := by
  subst s
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_vertex_d A b

/-- 概要：頂点因子に対応するテンソル境界項は零（BF §2.2.7）。
方針：指定因子まで帰納し、頂点の境界の零性とテンソルの零性を使う。
規約：指定位置より前の符号は任意でよい。
使われ方：辺の因子だけからなる境界和へ絞る。 -/
lemma tensorBoundaryTerm_eq_zero_of_vertex (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (k : Fin n)
    (b : Fin 2) (hf : f k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm A n f k = 0 := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    revert hf
    refine Fin.cases ?_ (fun j => ?_) k
    · intro hf
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm, Fin.cases_zero]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_d_eq_zero_of_vertex A (f 0) b hf,
        TensorProduct.zero_tmul, map_zero]
    · intro hf
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm, Fin.cases_succ]
      rw [ih (fun i => f i.succ) j hf, TensorProduct.tmul_zero, map_zero, smul_zero]

/-- 概要：全因子が頂点なら区間テンソルの生成元は閉じている（BF §2.2.7）。
方針：全因子の境界項が零となることを有限和に適用する。
規約：各因子の頂点は互いに異なってもよい。空族も含む。
使われ方：余演算の端点評価の微分条件。 -/
lemma tensorVector_d_eq_zero_of_vertices (n : ℕ) (b : Fin n → Fin 2) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex (b i)) : ℤ))
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex (b i)) : ℤ) + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex (b i))) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector_d]
  apply Finset.sum_eq_zero
  intro k _
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm_eq_zero_of_vertex A n _ k (b k) rfl

/-- 概要：テンソルの境界和は辺である因子だけに制限できる（BF §2.2.7）。
方針：区間の面の三分類と頂点因子の境界の零性を使う。
規約：集合のフィルタで辺因子の位置を選ぶ。
使われ方：語の削除と対応させる非零な境界項を取り出す。 -/
lemma tensorVector_d_eq_sum_edges (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => f k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm A n f k := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector_d, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : f k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge
  · simp only [hk, ite_true]
  · rw [ite_eq_right hk]
    rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplex_cases (f k) with h | h | h
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm_eq_zero_of_vertex A n f k 0 h
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm_eq_zero_of_vertex A n f k 1 h
    · exact False.elim (hk h)

/-- 概要：指定総次数への移送はテンソル生成元の閉性を保つ（BF §2.2.7）。
方針：総次数の等式を消去し、反射的な移送を簡約する。
規約：整数コチェイン微分の次の次数も同時に揃える。
使われ方：頂点の切断成分の閉性を固定した次数で使う。 -/
lemma tensorVectorOfDegree_d_eq_zero (n q : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f = q)
    (hf : (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ))
      (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f) = 0) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-(q : ℤ)) (-(q : ℤ) + 1)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n q f h) = 0 := by
  subst q
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree_refl] using hf

/-- 概要：先頭の辺因子の境界項は終点・始点のテンソルの差（BF §2.2.7）。
方針：辺の境界を二端点の差へ置き換え、テンソルと包含の線形性を使う。
規約：後続の族は任意。先頭より前の Koszul 符号はない。
使われ方：切断項の辺因子を頂点へ置換する比較の基礎。 -/
lemma tensorBoundaryTerm_zero_edge (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm A (n + 1) (Fin.cons _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge f) 0 =
      ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) 0 (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) (Fin.cons _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge f) : ℤ) + 1)
          (by
            change (0 : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) =
              -((1 + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℕ) : ℤ) + 1
            omega)
          ((show (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0 from _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 1)) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f) -
      ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) 0 (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) (Fin.cons _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge f) : ℤ) + 1)
          (by
            change (0 : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) =
              -((1 + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℕ) : ℤ) + 1
            omega)
          ((show (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0 from _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 0)) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f) := by
  change ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) 0 (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ))
    (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) (Fin.cons _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge f) : ℤ) + 1) _
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d (-1) 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f) = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_edge_d_sub, TensorProduct.sub_tmul, map_sub]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
