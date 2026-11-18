module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorVectors
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceBoundaries
public import Mathlib.Data.Fin.Tuple.Basic

/-!
模型。文献の定義との比較は後で
# 出力族の前方次数と一因子置換

概要：Berger–Fresse §2.2.7 の因子境界の符号と端点への置換の次数を計算する。
方針：有限和を先頭と残り、または指定位置と残りに分ける。
規約：前方次数は指定因子を含まない。
使われ方：辺因子を端点に置き換えたテンソルを境界の次数へ置く。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open scoped _root_.BigOperators

/-- 概要：指定因子より前の出力次数の和（BF §2.2.7）。
方針：色順の前方位置で有限和を取る。
規約：指定因子自身は含まない。
使われ方：その因子を微分する Koszul 符号。 -/
def prefixDegree (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (k : Fin n) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < k), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f j)

/-- 概要：先頭因子の前方次数は零（BF §2.2.7）。
方針：零より前の位置がないことを使う。
規約：任意の後続族。
使われ方：先頭の辺の境界は追加の符号を持たない。 -/
@[simp] lemma prefixDegree_zero (n : ℕ) (f : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree (n + 1) f 0 = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree]

/-- 概要：後続因子の前方次数は先頭次数と後続族の前方次数の和（BF §2.2.7）。
方針：有限和を零位置と succ の像へ分ける。
規約：色順を保つ。
使われ方：境界項の再帰的な符号を前方次数の符号へまとめる。 -/
@[simp] lemma prefixDegree_succ (n : ℕ) (f : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (k : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree (n + 1) f k.succ =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f 0) + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree n (fun i => f i.succ) k := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree, Finset.sum_filter, Fin.sum_univ_succ, Fin.succ_pos,
    ite_true, Fin.succ_lt_succ_iff]

/-- 概要：一因子置換の総次数は置換前後のその因子の次数差で決まる（BF §2.2.7）。
方針：全次数和を指定位置と残りへ分け、残りの一致を使う。
規約：任意の二つの非退化面の間の置換。
使われ方：辺から端点への置換で全次数が一つ下がることを得る。 -/
lemma tupleDegree_update (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (k : Fin n) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (Function.update f k s) + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f k) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_eq_sum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_eq_sum]
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (Function.update f k s j)) (Finset.mem_univ k)]
  rw [← Finset.add_sum_erase Finset.univ (fun j => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f j)) (Finset.mem_univ k)]
  have hs : (∑ j ∈ Finset.univ.erase k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (Function.update f k s j)) =
      ∑ j ∈ Finset.univ.erase k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [Function.update_self, hs]
  omega

/-- 概要：辺因子を端点へ置換すると総鎖次数は一つ下がる（BF §2.2.7）。
方針：一般の一因子置換の次数式へ辺と頂点の次数を代入する。
規約：指定因子が辺である証明が必要。
使われ方：端点置換のテンソルを元の境界の次数成分へ送る。 -/
lemma tupleDegree_update_edge (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (k : Fin n)
    (hf : f k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (Function.update f k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) + 1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f := by
  simpa only [hf, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_edge, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex, Nat.add_zero]
    using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_update n f k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
