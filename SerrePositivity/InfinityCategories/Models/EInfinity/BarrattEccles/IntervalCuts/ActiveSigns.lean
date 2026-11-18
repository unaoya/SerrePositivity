module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutValidity
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutSigns

/-!
模型。文献の定義との比較は後で
# 非退化な一単体切断の活動位置と符号

概要：Berger–Fresse §2.2.3–4 の Δ¹ の非零切断では位置符号が一となる。
方針：全区切りが切断点より前にあり、次数一の区間は区切りと切断点だけであることを使う。
規約：元の一般の切断符号の定義を変更せず、非退化条件の下で簡約する。
使われ方：χ の削除符号と出力テンソルの辺の交換符号の比較。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：非零な Δ¹ の辺の切断の位置指数は零（BF §2.2.4）。
方針：各内側区間は切断点より前なので右端点は零。
規約：退化な切断については主張しない。
使われ方：切断符号を区間交換の Koszul 符号だけへ簡約する。 -/
lemma edgePositionExponent_eq_zero {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePositionExponent u p = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun hi => (not_lt_of_ge hi.2) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_pivot h hi.1))

/-- 概要：非零な辺の切断の符号は区間交換だけで決まる（BF §2.2.4）。
方針：位置指数の零性を元の符号へ代入する。
規約：整数符号で述べる。
使われ方：削除微分との符号比較。 -/
lemma edgeSign_of_nondegenerate {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u p = (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePermutationExponent u p := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePositionExponent_eq_zero h, Nat.add_zero]

/-- 概要：符号長一の候補となる元位置の集合（BF §2.2.3）。
方針：全区切りの集合へ切断点を加える。
規約：退化な場合でも集合自体は定義する。
使われ方：辺の出力色と対応する位置を取り出す。 -/
def activePositions {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) : Finset (Fin l) :=
  insert p (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u))

/-- 概要：非零切断の活動位置は全て切断点以下（BF §2.2.3）。
方針：切断点か区切りかに分ける。
規約：切断点以外は厳密に前にある。
使われ方：活動位置上の色の単射性。 -/
lemma activePosition_le_pivot {n l : ℕ} {u : Fin l → Fin n} {p i : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (hi : i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u p) : i ≤ p := by
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact le_rfl
  · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_pivot h (Finset.mem_filter.mp hi).2).le

/-- 概要：非零切断の活動位置は互いに異なる色を持つ（BF §2.2.3）。
方針：活動位置が左側にあることと左側の単射性を使う。
規約：元位置集合上の単射性で述べる。
使われ方：活動位置と辺の出力因子の全単射の単射側。 -/
lemma activePositions_injOn {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : Set.InjOn u (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u p) := by
  intro i hi j hj hij
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h i j (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot h hi)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot h hj) hij

/-- 概要：非零切断の符号長は活動位置で一、それ以外で零（BF §2.2.3）。
方針：切断点が区切りでないことを使い、区間長の二つの加数を比較する。
規約：同じ位置の寄与が二にならない。
使われ方：交換指数を活動位置の色の逆転の個数へ移す。 -/
lemma edgeIntervalLength_of_nondegenerate {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (i : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeIntervalLength u p i = if i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u p then 1 else 0 := by
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.not_caesura_pivot h
  by_cases hi : i = p
  · subst i
    simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeIntervalLength, hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions]
  · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeIntervalLength, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, hi]

/-- 概要：次数 d の語の非零切断の活動位置は d+1 個（BF §2.2.3）。
方針：d 個の区切りに、それらに属さない切断点を加える。
規約：全 arity・全次数。
使われ方：出力辺の個数と削除位置の添字を比較する。 -/
lemma activePositions_card {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p).card = d + 1 := by
  have hp : p ∉ Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.not_caesura_pivot h
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, Finset.card_insert_of_notMem hp]
  have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.card_caesuras_basisWord u
  simpa only [Fintype.card_subtype] using congrArg (fun r : ℕ => r + 1) hc

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
