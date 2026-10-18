module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSign
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.BigOperators.Fin

/-!
# 二つの有限ブロックの交換の符号

概要：Berger–Fresse §1.1.3 の二入力の交換で現れる符号を計算する。
方針：ブロックの交換の逆転は異なるブロックの全ての対にちょうど一度現れる。
規約：長さ p と q のブロックを交換し、全辺数の型を元へ移送する。
使われ方：shuffle の方向交換の Koszul 符号を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：最初の p 個と残りの q 個を交換する置換（Berger–Fresse §1.1.3）。
方針：finAddFlip の終域を加法の交換則で元へ戻す。
規約：各ブロック内の順序は保つ。
使われ方：shuffle の方向交換を置換の積で記述する。 -/
def blockExchangePermutation (p q : ℕ) : Equiv.Perm (Fin (p + q)) :=
  finAddFlip.trans (finCongr (Nat.add_comm q p))

/-- 概要：交換後の最初のブロックの辺番号の値（Berger–Fresse §1.1.3）。
方針：finAddFlip の左ブロックでの公式を使う。
規約：値は q+a である。
使われ方：交換による逆転の対を数える。 -/
@[simp] lemma blockExchangePermutation_castAdd_val (p q : ℕ) (a : Fin p) :
    (blockExchangePermutation p q (Fin.castAdd q a)).val = q + a.val := by
  simp [blockExchangePermutation, Nat.add_comm]

/-- 概要：交換後の最後のブロックの辺番号の値（Berger–Fresse §1.1.3）。
方針：finAddFlip の右ブロックでの公式を使う。
規約：値はブロック内の番号 a である。
使われ方：交換による逆転の対を数える。 -/
@[simp] lemma blockExchangePermutation_natAdd_val (p q : ℕ) (a : Fin q) :
    (blockExchangePermutation p q (Fin.natAdd p a)).val = a.val := by
  simp [blockExchangePermutation]

/-- 概要：有限順序の初期区間上の積を全体上の条件付き積で表す（Berger–Fresse §1.1.3）。
方針：初期区間を univ の filter として書く。
規約：初期区間の外の因子は1とする。
使われ方：置換の符号の積を二つのブロックへ分割する。 -/
lemma prod_Iio_eq_univ_ite {N : ℕ} (j : Fin N) (f : Fin N → ℤˣ) :
    (∏ i ∈ Finset.Iio j, f i) = ∏ i, if i < j then f i else 1 := by
  have h : Finset.Iio j = Finset.univ.filter (fun i => i < j) := by ext i; simp
  rw [h, Finset.prod_filter]

/-- 概要：二つのブロックの交換の符号は (−1)^(pq) である（Berger–Fresse §1.1.3）。
方針：符号の逆転の対による公式を二つの入力ブロックに分けて計算する。
規約：p または q が0でも同じ公式が成り立つ。
使われ方：shuffle の方向交換および並列結合則の Koszul 符号となる。 -/
lemma blockExchangePermutation_sign (p q : ℕ) :
    Equiv.Perm.sign (blockExchangePermutation p q) = (-1 : ℤˣ) ^ (p * q) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  simp_rw [prod_Iio_eq_univ_ite]
  rw [Fin.prod_univ_add]
  have hfirst (j : Fin p) :
      (∏ i : Fin (p + q), if i < Fin.castAdd q j then
        (if blockExchangePermutation p q i < blockExchangePermutation p q (Fin.castAdd q j)
          then (1 : ℤˣ) else -1) else 1) = 1 := by
    rw [Fin.prod_univ_add]
    have h₁ : (∏ i : Fin p, if Fin.castAdd q i < Fin.castAdd q j then
        (if blockExchangePermutation p q (Fin.castAdd q i) <
          blockExchangePermutation p q (Fin.castAdd q j) then (1 : ℤˣ) else -1) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp only [Fin.lt_def, Fin.val_castAdd, blockExchangePermutation_castAdd_val]
      split_ifs <;> first | rfl | omega
    have h₂ : (∏ i : Fin q, if Fin.natAdd p i < Fin.castAdd q j then
        (if blockExchangePermutation p q (Fin.natAdd p i) <
          blockExchangePermutation p q (Fin.castAdd q j) then (1 : ℤˣ) else -1) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      have hj := j.isLt
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd,
        blockExchangePermutation_natAdd_val, blockExchangePermutation_castAdd_val]
      split_ifs <;> first | rfl | omega
    rw [h₁, h₂, one_mul]
  have hlast (j : Fin q) :
      (∏ i : Fin (p + q), if i < Fin.natAdd p j then
        (if blockExchangePermutation p q i < blockExchangePermutation p q (Fin.natAdd p j)
          then (1 : ℤˣ) else -1) else 1) = (-1 : ℤˣ) ^ p := by
    rw [Fin.prod_univ_add]
    have h₁ : (∏ i : Fin p, if Fin.castAdd q i < Fin.natAdd p j then
        (if blockExchangePermutation p q (Fin.castAdd q i) <
          blockExchangePermutation p q (Fin.natAdd p j) then (1 : ℤˣ) else -1) else 1) =
        (-1 : ℤˣ) ^ p := by
      have he (i : Fin p) : (if Fin.castAdd q i < Fin.natAdd p j then
          (if blockExchangePermutation p q (Fin.castAdd q i) <
            blockExchangePermutation p q (Fin.natAdd p j) then (1 : ℤˣ) else -1) else 1) = -1 := by
        have hi := i.isLt
        have hj := j.isLt
        simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd,
          blockExchangePermutation_natAdd_val, blockExchangePermutation_castAdd_val]
        split_ifs <;> first | rfl | omega
      simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h₂ : (∏ i : Fin q, if Fin.natAdd p i < Fin.natAdd p j then
        (if blockExchangePermutation p q (Fin.natAdd p i) <
          blockExchangePermutation p q (Fin.natAdd p j) then (1 : ℤˣ) else -1) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp only [Fin.lt_def, Fin.val_natAdd, blockExchangePermutation_natAdd_val]
      split_ifs <;> first | rfl | omega
    rw [h₁, h₂, mul_one]
  simp only [hfirst, hlast, Finset.prod_const_one, one_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]

end SerrePositivity.EInfinity.BarrattEccles
