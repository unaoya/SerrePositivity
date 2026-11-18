module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AdjacentSlotFirst

/-!
模型。文献の定義との比較は後で
# 隣接する二入力の交換の二回の代入後の出力

概要：Berger–Moerdijk §1 の隣接入力の互換を二回の代入後の四区間で計算する。
方針：最初の代入後の置換を二回目の挿入分解で延長する。
規約：前方 p 個と後方 q 個の入力を保ち、内側の arity を a,b とする。
使われ方：出力の全単射を標準の二ブロック交換と比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：最初の代入後の置換を二回目の代入後へ延長する（Berger–Moerdijk §1）。
方針：位置 p+a への b 入力の代入に外側置換を延長する。
規約：出力の arity の表記は p+q+a+b。
使われ方：出力の前方、左、右、後方の四区間の計算に使う。 -/
def operadAdjacentSlotSecond (p q a b : ℕ) : Equiv.Perm (Fin (((p + q) + a) + b)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation ((p + q) + a) b ⟨p + a, by omega⟩
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst p q a)

/-- 概要：二回の代入後の隣接交換は前方の入力を固定する（Berger–Moerdijk §1）。
方針：挿入区間の前に残る入力に最初の代入後の計算を適用する。
規約：前方の入力を Fin p で指定する。
使われ方：出力の全単射の前方の区間を計算する。 -/
lemma operadAdjacentSlotSecond_before (p q a b : ℕ) (x : Fin p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond p q a b ⟨x.val, by omega⟩ = ⟨x.val, by omega⟩ := by
  have hx : x.val < p := x.isLt
  have hb : x.val < p + a := by omega
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst_before p q a x
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst_slot p q a
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv, hb, hx, hp, hs]

/-- 概要：二回の代入後の左ブロックは右ブロックの後へ移る（Berger–Moerdijk §1）。
方針：最初の代入区間の移動を残りの入力の挿入分解へ反映する。
規約：ブロック内の順序を保つ。
使われ方：出力の全単射の左ブロックを計算する。 -/
lemma operadAdjacentSlotSecond_left (p q a b : ℕ) (x : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond p q a b ⟨p + x.val, by omega⟩ =
      ⟨p + b + x.val, by omega⟩ := by
  have hb : p + x.val < p + a := by have := x.isLt; omega
  have hpost : ¬p + 1 + x.val < p := by omega
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst_inserted p q a x
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst_slot p q a
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv, hb, hp, hs, hpost]
  omega

/-- 概要：二回の代入後の右ブロックは左ブロックの前へ移る（Berger–Moerdijk §1）。
方針：二回目の挿入区間における外側置換の式を使う。
規約：右ブロックの内部の順序を保つ。
使われ方：出力の全単射の右ブロックを計算する。 -/
lemma operadAdjacentSlotSecond_right (p q a b : ℕ) (x : Fin b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond p q a b ⟨p + a + x.val, by omega⟩ =
      ⟨p + x.val, by omega⟩ := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_inside ((p + q) + a) b ⟨p + a, by omega⟩
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst p q a) x
  have hv := congrArg Fin.val h
  simp only [Fin.val_mk, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst_slot] at hv
  exact Fin.ext hv

/-- 概要：二回の代入後の隣接交換は後方の入力を固定する（Berger–Moerdijk §1）。
方針：挿入区間より後の残りの入力を最初の代入後の式で計算する。
規約：終域の長さは交換後の b+a の順で記述する。
使われ方：出力の全単射の後方の区間を計算する。 -/
lemma operadAdjacentSlotSecond_after (p q a b : ℕ) (x : Fin q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond p q a b ⟨p + a + b + x.val, by omega⟩ =
      ⟨p + b + a + x.val, by omega⟩ := by
  have h₀ : ¬p + a + b + x.val < p + a := by omega
  have h₁ : ¬p + a + b + x.val < p + a + b := by omega
  have hv : (p + a + b + x.val) + 1 - b = p + a + 1 + x.val := by omega
  have hpost : ¬p + a + 1 + x.val < p := by omega
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst_after p q a x
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst_slot p q a
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv, h₀, h₁, hv, hpost, hp, hs]
  omega

/-- 概要：隣接入力の交換後の出力を交換後の arity へ移す（Berger–Moerdijk §1）。
方針：二回の代入後の置換の後に標準の長さの移送を合成する。
規約：始域は p+q+a+b、終域は p+q+b+a。
使われ方：対称列に適用する出力の有限全単射となる。 -/
def operadAdjacentSlotOutput (p q a b : ℕ) :
    Fin (((p + q) + a) + b) ≃ Fin (((p + q) + b) + a) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond p q a b).trans
    (finCongr (by omega : ((p + q) + a) + b = ((p + q) + b) + a))

/-- 概要：隣接入力の出力の全単射は二位置への一般の合成の出力と一致する（Berger–Moerdijk §1）。
方針：二回目の代入位置の式 p+1+a-1 を p+a へ正規化する。
規約：二位置は p と p+1。
使われ方：二位置への合成の外側等変性の出力を四区間の計算式へ移す。 -/
lemma operadAdjacentSlotOutput_eq_twoSlot (p q a b : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotOutput p q a b =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotOutputEquiv (p + q) a b ⟨p, by omega⟩ ⟨p + 1, by omega⟩
        (by change p < p + 1; omega) := by
  have he : (⟨(p + 1) + a - 1, by omega⟩ : Fin (((p + q) + a) + 1)) =
      ⟨p + a, by omega⟩ := by apply Fin.ext; dsimp; omega
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotOutput, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotOutputEquiv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst, he]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
