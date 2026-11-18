module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionCounts
public import SerrePositivity.GroupTheory.Coxeter.TypeA
public import Mathlib.Data.Finset.SymmDiff

/-!
模型。文献の定義との比較は後で
# 隣接色交換が逆転対へ与える変化

概要：Berger–Fresse §2.2.4 の切断符号の隣接色交換を有限逆転集合で扱う。
方針：色順の反転が変わるのは交換する二色の対だけであることを使う。
規約：元の位置順は固定する。
使われ方：切断係数と出力の Koszul 隣接交換符号の一致。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators _root_.symmDiff

private lemma nat_adjacent_order_change (a x y : ℕ) :
    (((if y = a then a + 1 else if y = a + 1 then a else y) <
      (if x = a then a + 1 else if x = a + 1 then a else x) ∧ ¬y < x) ∨
      (y < x ∧ ¬(if y = a then a + 1 else if y = a + 1 then a else y) <
        (if x = a then a + 1 else if x = a + 1 then a else x))) ↔
      (x = a ∧ y = a + 1) ∨ (x = a + 1 ∧ y = a) := by
  split_ifs <;> omega

/-- 概要：隣接色交換の値を自然数で評価する（BF §2.2.4）。
方針：交換される二点と残りに分ける。
規約：有限添字の値は零始まり。
使われ方：隣接交換の順序比較を自然数算術へ戻す。 -/
lemma adjacentTransposition_val (n : ℕ) (a : Fin n) (x : Fin (n + 1)) :
    (adjacentTransposition a x).val =
      if x.val = a.val then a.val + 1 else if x.val = a.val + 1 then a.val else x.val := by
  by_cases h0 : x = a.castSucc
  · subst x
    simp [adjacentTransposition]
  · by_cases h1 : x = a.succ
    · subst x
      simp [adjacentTransposition]
    · have hv0 : x.val ≠ a.val := fun h => h0 (Fin.ext h)
      have hv1 : x.val ≠ a.val + 1 := fun h => h1 (Fin.ext h)
      rw [adjacentTransposition, Equiv.swap_apply_of_ne_of_ne h0 h1]
      simp only [ite_eq_right hv0, ite_eq_right hv1]

/-- 概要：隣接色交換で大小関係が変わるのはその二色の対だけ（BF §2.2.4）。
方針：交換される二点との一致で場合分けし、隣接性で中間の色を除く。
規約：等しい色の対は変化しない。
使われ方：逆転集合の対称差の所属判定。 -/
lemma adjacentTransposition_order_change (n : ℕ) (a : Fin n) (x y : Fin (n + 1)) :
    ((adjacentTransposition a y < adjacentTransposition a x ∧ ¬y < x) ∨
      (y < x ∧ ¬adjacentTransposition a y < adjacentTransposition a x)) ↔
      (x = a.castSucc ∧ y = a.succ) ∨ (x = a.succ ∧ y = a.castSucc) := by
  simpa only [Fin.lt_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.adjacentTransposition_val, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nat_adjacent_order_change a.val x.val y.val

/-- 概要：指定位置集合内の色の逆転対の有限集合（BF §2.2.4）。
方針：二位置の積から元位置順と色の逆順を満たす対を選ぶ。
規約：一つの非順序対は一回だけ数える。
使われ方：逆転数を集合の濃度として計算する。 -/
def positionInversions {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l)) :
    Finset (Fin l × Fin l) :=
  (s ×ˢ s).filter (fun ij => ij.1 < ij.2 ∧ u ij.2 < u ij.1)

/-- 概要：逆転対の濃度は既存の逆転数（BF §2.2.4）。
方針：有限集合の濃度を零一指示関数の和に展開する。
規約：色の単射性は不要。
使われ方：切断符号の指数を集合の対称差で比較する。 -/
lemma card_positionInversions {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions u s).card = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions, Finset.card_filter, Finset.sum_product,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm]

/-- 概要：隣接色交換の逆転集合の対称差は交換二色の位置対（BF §2.2.4）。
方針：各対の所属を展開して色順の変化の判定を適用する。
規約：元位置の順序は増加順に一回だけ数える。
使われ方：切断符号の変化を交換二色の活動性へ帰着する。 -/
lemma positionInversions_symmDiff_adjacent {n l : ℕ} (a : Fin n)
    (u : Fin l → Fin (n + 1)) (s : Finset (Fin l)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions (adjacentTransposition a ∘ u) s) ∆ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions u s =
      (s ×ˢ s).filter (fun ij => ij.1 < ij.2 ∧
        ((u ij.1 = a.castSucc ∧ u ij.2 = a.succ) ∨
          (u ij.1 = a.succ ∧ u ij.2 = a.castSucc))) := by
  ext ij
  simp only [Finset.mem_symmDiff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions, Finset.mem_filter,
    Finset.mem_product, Function.comp_apply]
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.adjacentTransposition_order_change n a (u ij.1) (u ij.2)
  tauto

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
