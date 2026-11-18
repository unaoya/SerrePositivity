module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TwoSlotPermutations

/-!
模型。文献の定義との比較は後で
# 隣接する二入力の最初の代入後の交換

概要：Berger–Moerdijk §1 の隣接入力の互換を、最初の代入後の各入力で計算する。
方針：前方の入力、代入した区間、残った入力、後方の入力に分ける。
規約：前方 p 個と後方 q 個の入力を保持し、位置 p に a 入力の演算を代入する。
使われ方：二回の代入後の出力を二ブロックの交換と比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：隣接入力の互換を最初の代入後へ延長する（Berger–Moerdijk §1）。
方針：二位置の一般の置換で位置 p と p+1 を指定する。
規約：外側には p+q+2 個の入力がある。
使われ方：二回目の代入の前の入力を各区間で追跡する。 -/
def operadAdjacentSlotAfterFirst (p q a : ℕ) : Equiv.Perm (Fin (((p + q) + a) + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst (p + q) a ⟨p, by omega⟩ ⟨p + 1, by omega⟩

/-- 概要：最初の代入後の隣接交換は前方の入力を固定する（Berger–Moerdijk §1）。
方針：挿入区間より前の残りの入力における互換を評価する。
規約：前方の入力を Fin p で指定する。
使われ方：二回の代入後にも前方の入力が固定されることを示す。 -/
lemma operadAdjacentSlotAfterFirst_before (p q a : ℕ) (x : Fin p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst p q a ⟨x.val, by omega⟩ = ⟨x.val, by omega⟩ := by
  have hx : x.val < p := x.isLt
  have hx' : x.val < p + 1 := by omega
  have hn₀ : x.val ≠ p := by omega
  have hn₁ : x.val ≠ p + 1 := by omega
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst, Equiv.permCongr_def,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv,
    Equiv.swap_apply_def, Fin.ext_iff, hx, hx', hn₀, hn₁]

/-- 概要：最初に代入した区間は隣接する一入力の後へ移る（Berger–Moerdijk §1）。
方針：挿入分解の内側成分で互換を評価する。
規約：代入区間の内部の順序を保つ。
使われ方：二回目の代入後の左ブロックの位置を計算する。 -/
lemma operadAdjacentSlotAfterFirst_inserted (p q a : ℕ) (x : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst p q a ⟨p + x.val, by omega⟩ =
      ⟨p + 1 + x.val, by omega⟩ := by
  have hx : x.val < a := x.isLt
  have h₀ : ¬p + x.val < p := by omega
  have h₁ : p + x.val < p + a := by omega
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst, Equiv.permCongr_def,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv,
    Equiv.swap_apply_def, Fin.ext_iff, h₀, h₁]

/-- 概要：残る隣接入力は互換によって前方の代入位置へ移る（Berger–Moerdijk §1）。
方針：二位置の一般の代入位置の計算を適用する。
規約：a=0 も許す。
使われ方：二回目の代入の挿入位置を計算する。 -/
lemma operadAdjacentSlotAfterFirst_slot (p q a : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst p q a ⟨p + a, by omega⟩ = ⟨p, by omega⟩ := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst_remaining (p + q) a
    (⟨p, by omega⟩ : Fin ((p + q) + 2)) ⟨p + 1, by omega⟩ (by
      change p < p + 1
      omega)
  have he : (⟨(p + 1) + a - 1, by omega⟩ : Fin (((p + q) + a) + 1)) =
      ⟨p + a, by omega⟩ := by apply Fin.ext; dsimp; omega
  rw [he] at h
  exact h

/-- 概要：最初の代入後の隣接交換は後方の入力を固定する（Berger–Moerdijk §1）。
方針：代入区間の後の残りの入力を評価し、位置の加減算を整理する。
規約：後方の入力を Fin q で指定する。
使われ方：二回の代入後にも後方の入力が固定されることを示す。 -/
lemma operadAdjacentSlotAfterFirst_after (p q a : ℕ) (x : Fin q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst p q a ⟨p + a + 1 + x.val, by omega⟩ =
      ⟨p + a + 1 + x.val, by omega⟩ := by
  have h₀ : ¬p + a + 1 + x.val < p := by omega
  have h₁ : ¬p + a + 1 + x.val < p + a := by omega
  have hv : (p + a + 1 + x.val) + 1 - a = p + 2 + x.val := by omega
  have hn₀ : p + 2 + x.val ≠ p := by omega
  have hn₁ : p + 2 + x.val ≠ p + 1 := by omega
  have hpost : ¬p + 2 + x.val < p + 1 := by omega
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotAfterFirst, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst, Equiv.permCongr_def,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv,
    Equiv.swap_apply_def, Fin.ext_iff, h₀, h₁, hv, hn₀, hn₁, hpost]
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
