module

public import SerrePositivity.EInfinity.Operad.TensorFamilyAdjacentValues
public import SerrePositivity.EInfinity.Operad.SlotPermutations

/-!
# 先頭の入力ブロックを指定した位置へ動かす

概要：Berger–Moerdijk §1 の先頭の部分合成を任意位置へ移す入力置換を構成する。
方針：先頭 p 入力と続く a 入力を交換し、後半 b 入力を固定する。
規約：全体の長さを a+b+p と表し、p=0 も許す。
使われ方：入力代入射の置換則を三ブロックの連結と交換へ帰着する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity

/-- 概要：先頭 p 入力を続く a 入力の後へ動かす置換（Berger–Moerdijk §1）。
方針：三ブロックの交換を全体の arity の同じ表示へ移す。
規約：最後の b 入力を固定する。
使われ方：p=1 で外側の入力、p=n で代入後の入力を動かす。 -/
def operadMoveFirstBlock (a b p : ℕ) : Equiv.Perm (Fin (a + b + p)) :=
  (finCongr (by omega : a + b + p = p + (a + b))).trans
    ((operadFirstBlockSwap p a b).trans (finCongr (by omega : a + (p + b) = a + b + p)))

/-- 概要：先頭ブロックの移動を三つの入力区間で評価する（Berger–Moerdijk §1）。
方針：三ブロック交換の値の式と長さの移送の値の不変性を使う。
規約：最初の p 入力、続く a 入力、後半 b 入力の順に場合分けする。
使われ方：部分合成後の入力置換と座標ごとに比較する。 -/
lemma operadMoveFirstBlock_val (a b p : ℕ) (x : Fin (a + b + p)) :
    (operadMoveFirstBlock a b p x).val =
      if x.val < p then x.val + a else if x.val < p + a then x.val - p else x.val := by
  simp only [operadMoveFirstBlock, Equiv.trans_apply, finCongr_apply_coe,
    operadFirstBlockSwap_val]
  rfl

/-- 概要：一入力の先頭ブロックの移動は先頭を位置 a へ送る（Berger–Moerdijk §1）。
方針：値の式の先頭区間を評価する。
規約：外側の入力数は a+b+1。
使われ方：先頭の部分合成の挿入位置の移動を計算する。 -/
lemma operadMoveFirstBlock_zero (a b : ℕ) :
    operadMoveFirstBlock a b 1 0 = ⟨a, by omega⟩ := by
  apply Fin.ext
  simp only [operadMoveFirstBlock_val, Fin.val_zero, Nat.zero_lt_one, ite_true, Nat.zero_add]

/-- 概要：挿入分解の残りの入力に対する逆写像の値（Berger–Moerdijk §1）。
方針：挿入分解の逆写像の定義を評価する。
規約：元の外側の入力は指定位置 i を除く部分型で表す。
使われ方：外側の置換が挿入区間以外の入力へ与える移動を計算する。 -/
lemma operadInsertionEquiv_remaining_val (m n : ℕ) (i : Fin (m + 1))
    (j : {j : Fin (m + 1) // j ≠ i}) :
    ((operadInsertionEquiv m n i).symm (Sum.inl j)).val =
      if j.val.val < i.val then j.val.val else j.val.val + n - 1 := by
  unfold operadInsertionEquiv
  dsimp
  split_ifs <;> rfl

/-- 概要：一入力の先頭移動を代入後へ延長すると先頭 n 入力のブロック移動となる（Berger–Moerdijk §1）。
方針：挿入区間内では内部の順序を保ち、残りの入力は外側の置換に従うことを使う。
規約：代入位置は零、移動後の位置は a。
使われ方：部分合成の外側置換をテンソル冪の三ブロック交換へ同定する。 -/
lemma operadOuterPermutation_moveFirst (a b n : ℕ) :
    operadOuterPermutation (a + b) n 0 (operadMoveFirstBlock a b 1) =
      operadMoveFirstBlock a b n := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  rw [operadMoveFirstBlock_val]
  by_cases hx : x.val < n
  · have he : x = (⟨(0 : Fin (a + b + 1)).val + (⟨x.val, hx⟩ : Fin n).val, by omega⟩ :
        Fin (a + b + n)) := by apply Fin.ext; simp
    rw [he, operadOuterPermutation_inside]
    simp only [Fin.val_zero, Nat.zero_add]
    rw [operadMoveFirstBlock_zero]
    simp only [hx, ite_true]
    omega
  · let j : {j : Fin (a + b + 1) // j ≠ (0 : Fin (a + b + 1))} :=
      ⟨⟨x.val + 1 - n, by omega⟩, by intro h; have h' := congrArg Fin.val h; dsimp at h'; omega⟩
    have he : (operadInsertionEquiv (a + b) n 0).symm (Sum.inl j) = x := by
      apply Fin.ext
      rw [operadInsertionEquiv_remaining_val]
      dsimp [j]
      omega
    have h := congrArg Fin.val
      (operadOuterPermutation_remaining (a + b) n 0 (operadMoveFirstBlock a b 1) j)
    rw [he, operadInsertionEquiv_remaining_val] at h
    change (operadOuterPermutation (a + b) n 0 (operadMoveFirstBlock a b 1) x).val =
      (if (operadMoveFirstBlock a b 1 j.val).val < (operadMoveFirstBlock a b 1 0).val then
        (operadMoveFirstBlock a b 1 j.val).val else
        (operadMoveFirstBlock a b 1 j.val).val + n - 1) at h
    rw [operadMoveFirstBlock_zero] at h
    rw [operadMoveFirstBlock_val] at h
    dsimp [j] at h
    split_ifs at h ⊢ <;> omega

end SerrePositivity.EInfinity
