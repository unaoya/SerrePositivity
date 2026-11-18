module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SlotPermutations

/-!
模型。文献の定義との比較は後で
# 異なる二入力の交換と代入後の置換

概要：Berger–Moerdijk §1 の外側等変性で、異なる二入力を交換した後の残りの代入位置を計算する。
方針：二入力の互換を最初の代入後へ延長し、残る入力の位置を追跡する。
規約：左の位置 i は右の位置 j より前とし、内側の arity は零でもよい。
使われ方：任意の外側 arity における二つの代入の外側等変性に使う。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：二入力の互換が最初の代入後に誘導する置換（Berger–Moerdijk §1）。
方針：挿入分解で互換を延長し、次の代入の arity の表記へ移す。
規約：最初に位置 i へ a 入力の演算を代入する。
使われ方：次に位置 j へ代入する演算の位置を交換後へ移す。 -/
def operadTwoSlotAfterFirst (m a : ℕ) (i j : Fin (m + 2)) :
    Equiv.Perm (Fin ((m + a) + 1)) :=
  (finCongr (by omega : (m + 1) + a = (m + a) + 1)).permCongr
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (m + 1) a i (Equiv.swap i j))

/-- 概要：最初の代入後の右の入力は、互換によって左の入力へ移る（Berger–Moerdijk §1）。
方針：挿入区間の後に残る入力を計算し、互換と逆の挿入分解を適用する。
規約：i<j とし、a=0 も含む。
使われ方：二回目の部分合成に外側等変性を適用する。 -/
lemma operadTwoSlotAfterFirst_remaining (m a : ℕ) (i j : Fin (m + 2))
    (hij : i.val < j.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst m a i j ⟨j.val + a - 1, by omega⟩ = ⟨i.val, by omega⟩ := by
  have h₀ : ¬j.val + a - 1 < i.val := by omega
  have h₁ : ¬j.val + a - 1 < i.val + a := by omega
  have hv : (j.val + a - 1) + 1 - a = j.val := by omega
  have hne : j.val ≠ i.val := by omega
  have hlt : i < j := hij
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst, Equiv.permCongr_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv, h₀, h₁, hv, Equiv.swap_apply_def,
    Fin.ext_iff, hne, hlt]

/-- 概要：二入力の互換を二回の代入後へ延長した全単射（Berger–Moerdijk §1）。
方針：最初の代入後の置換を二回目の代入後へ延長し、交換後の arity へ移す。
規約：始域の長さは m+a+b、終域は m+b+a。
使われ方：異なる二入力への代入の外側等変性の出力側を記述する。 -/
def operadTwoSlotOutputEquiv (m a b : ℕ) (i j : Fin (m + 2)) (_hij : i.val < j.val) :
    Fin ((m + a) + b) ≃ Fin ((m + b) + a) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (m + a) b ⟨j.val + a - 1, by omega⟩
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst m a i j)).trans
      (finCongr (by omega : (m + a) + b = (m + b) + a))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
