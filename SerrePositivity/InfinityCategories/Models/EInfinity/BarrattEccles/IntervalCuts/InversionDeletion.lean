module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionCounts
public import Mathlib.Algebra.Ring.NegOnePow

/-!
模型。文献の定義との比較は後で
# 活動位置の削除と交換符号

概要：Berger–Fresse §2.2.7 の符号比較に使う有限逆転数の削除公式を証明する。
方針：削除位置を含む逆転対を、元位置順と色順の二つの順位で数える。
規約：色は指定した位置集合上で単射。整数係数で全ての符号を比較する。
使われ方：χ の削除位置の符号とテンソルの出力色の境界符号を交換する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open scoped _root_.BigOperators

/-- 概要：指定位置より前にある位置の個数（BF §2.2.7）。
方針：有限集合を元位置順で切る。
規約：指定位置自身を含めない。
使われ方：語の削除で生じる位置の符号。 -/
def positionRank {l : ℕ} (s : Finset (Fin l)) (a : Fin l) : ℕ :=
  (s.filter (fun j => j < a)).card

/-- 概要：指定位置の色より小さい色の個数（BF §2.2.7）。
方針：有限な位置集合を色の大小で切る。
規約：同じ色は含めない。
使われ方：出力テンソルの辺因子の境界符号。 -/
def colorRank {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l)) (a : Fin l) : ℕ :=
  (s.filter (fun j => u j < u a)).card

/-- 概要：元位置と色の両方で指定位置より前にある個数（BF §2.2.7）。
方針：二つの順位条件の共通部分を数える。
規約：この個数の偶数倍だけが逆転数の差に残る。
使われ方：削除前後の符号一致を整数の偶奇へ帰着する。 -/
def lowerRank {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l)) (a : Fin l) : ℕ :=
  (s.filter (fun j => j < a ∧ u j < u a)).card

private lemma inversion_rank_pointwise {n l : ℕ} (u : Fin l → Fin n)
    (s : Finset (Fin l)) (hu : Set.InjOn u s) (a : Fin l) (ha : a ∈ s)
    (j : Fin l) (hj : j ∈ s) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a j + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u j a +
        2 * (if j < a ∧ u j < u a then 1 else 0) =
      (if j < a then 1 else 0) + (if u j < u a then 1 else 0) := by
  by_cases hja : j = a
  · subst j
    simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm]
  have hc : u j ≠ u a := fun h => hja (hu hj ha h)
  rcases lt_or_gt_of_ne hja with hp | hp <;>
    rcases lt_or_gt_of_ne hc with hc | hc <;>
    simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hp, hc, not_lt_of_ge hp.le, not_lt_of_ge hc.le]

/-- 概要：逆転数の削除差と二つの順位の整数的な釣り合い（BF §2.2.7）。
方針：指定位置を含む二種類の対を点ごとに数え、有限和を取る。
規約：余分な項は二つの順位条件の共通部分の二倍。
使われ方：切断の交換符号と削除・境界符号の一致。 -/
lemma positionInversionCount_erase_balance {n l : ℕ} (u : Fin l → Fin n)
    (s : Finset (Fin l)) (hu : Set.InjOn u s) (a : Fin l) (ha : a ∈ s) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s + 2 * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lowerRank u s a =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.erase a) + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank s a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank u s a := by
  have hs := Finset.sum_congr rfl (fun j hj => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.inversion_rank_pointwise u s hu a ha j hj)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole] at hs
  change (∑ j ∈ s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a j) +
      (∑ j ∈ s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u j a) + 2 * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lowerRank u s a =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank s a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank u s a at hs
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_erase u s a ha]
  omega

/-- 概要：位置を一つ削除すると元位置符号と出力色の符号が交換する（BF §2.2.7）。
方針：逆転数と二つの順位の釣り合いから、両指数の差が偶数であることを使う。
規約：整数の −1 冪。全ての有限な単射色族に成立する。
使われ方：χ の削除係数と切断テンソルの辺の境界係数の比較。 -/
lemma positionInversionSign_erase {n l : ℕ} (u : Fin l → Fin n)
    (s : Finset (Fin l)) (hu : Set.InjOn u s) (a : Fin l) (ha : a ∈ s) :
    (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s * (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank u s a =
      (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank s a * (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.erase a) := by
  have hb := congrArg (fun r : ℕ => (r : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_erase_balance u s hu a ha)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hb
  have hu' : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank u s a : ℕ) : ℤ).negOnePow =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank s a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.erase a) : ℕ) : ℤ).negOnePow := by
    apply (Int.negOnePow_eq_iff _ _).2
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank u s a : ℤ) - (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lowerRank u s a : ℤ), ?_⟩
    simp only [Nat.cast_add]
    omega
  have hp := congrArg (fun z : ℤˣ => (z : ℤ)) hu'
  simpa only [Int.coe_negOnePow_natCast, pow_add] using hp

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
