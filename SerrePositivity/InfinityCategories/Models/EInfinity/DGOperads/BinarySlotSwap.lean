module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SlotPermutations

/-!
模型。文献の定義との比較は後で
# 二入力の交換が代入後の入力に誘導する全単射

概要：Berger–Moerdijk §1 の外側等変性で、二入力の交換を代入後のブロック交換と比較する。
方針：最初の代入後の残りの入力と挿入区間で置換を計算し、次の代入へ移す。
規約：ブロックの長さは 0 を含む。arity の移送は Fin の標準同値を用いる。
使われ方：二入力の全合成の外側等変性の出力の全単射を同定する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：二つの入力を交換する置換（Berger–Moerdijk §1）。
方針：Fin 2 の二点の交換を用いる。
規約：位置は 0 と 1。
使われ方：二入力のオペラッド合成の外側置換となる。 -/
def operadTwoSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- 概要：二入力の交換は先頭を二番目へ送る（Berger–Moerdijk §1）。
方針：二点の交換を評価する。
規約：arity は 2。
使われ方：外側等変性の挿入位置を計算する。 -/
@[simp] lemma operadTwoSwap_zero : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwap 0 = 1 := Equiv.swap_apply_left _ _

/-- 概要：二入力の交換は二番目を先頭へ送る（Berger–Moerdijk §1）。
方針：二点の交換を評価する。
規約：arity は 2。
使われ方：代入後に残る入力の位置を計算する。 -/
@[simp] lemma operadTwoSwap_one : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwap 1 = 0 := Equiv.swap_apply_right _ _

/-- 概要：長さ a と b の二つのブロックを交換する全単射（Berger–Moerdijk §1）。
方針：標準有限集合の直和を交換してから連結する。
規約：始域の長さは a+b、終域の長さは b+a。
使われ方：二入力の外側交換に対応する出力の全単射となる。 -/
def operadBlockSwap (a b : ℕ) : Fin (a + b) ≃ Fin (b + a) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin a) (Fin b)).trans finSumFinEquiv)

/-- 概要：左ブロックの入力は交換後に右ブロックへ送られる（Berger–Moerdijk §1）。
方針：有限直和の左成分を交換して評価する。
規約：入力の内部順序は保つ。
使われ方：出力のブロック交換を各入力で計算する。 -/
lemma operadBlockSwap_left (a b : ℕ) (j : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b (j.castAdd b) = j.natAdd b := by
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b (finSumFinEquiv (Sum.inl j)) = _
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap]

/-- 概要：右ブロックの入力は交換後に左ブロックへ送られる（Berger–Moerdijk §1）。
方針：有限直和の右成分を交換して評価する。
規約：入力の内部順序は保つ。
使われ方：出力のブロック交換を各入力で計算する。 -/
lemma operadBlockSwap_right (a b : ℕ) (j : Fin b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b (j.natAdd a) = j.castAdd a := by
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b (finSumFinEquiv (Sum.inr j)) = _
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap]

/-- 概要：二入力を交換すると先頭に代入した入力ブロックは一つ後ろへ移る（Berger–Moerdijk §1）。
方針：外側置換の挿入区間内の計算則を使う。
規約：ブロックの内部の位置は保つ。
使われ方：一段目の代入の外側置換を計算する。 -/
lemma operadTwoSwap_inserted (a : ℕ) (j : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation 1 a 0 _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwap ⟨j.val, by omega⟩ =
      ⟨1 + j.val, by omega⟩ := by
  simpa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwap] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_inside 1 a 0 _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwap j

/-- 概要：二入力を交換すると最初の代入後の残りの入力は先頭へ移る（Berger–Moerdijk §1）。
方針：挿入分解の残りの成分を明示的に評価する。
規約：最初の入力への代入後の残りの位置は a。
使われ方：二段目の代入位置を先頭へ移す。 -/
lemma operadTwoSwap_remaining (a : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation 1 a 0 _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwap ⟨a, by omega⟩ = 0 := by
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwap, -Fin.val_fin_lt]

/-- 概要：最初の代入後の外側交換を次の部分合成の arity へ移す（Berger–Moerdijk §1）。
方針：1+a と 0+a+1 の標準有限集合を同一視する。
規約：置換の始域は二段目の部分合成の外側 arity。
使われ方：二段目の外側等変性に適用する置換となる。 -/
def operadTwoSwapAfterFirst (a : ℕ) : Equiv.Perm (Fin ((0 + a) + 1)) :=
  (finCongr (by omega : 1 + a = (0 + a) + 1)).permCongr
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation 1 a 0 _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwap)

private lemma finCongr_permCongr_val {r s : ℕ} (h : r = s) (σ : Equiv.Perm (Fin r))
    (x : Fin s) :
    (((finCongr h).permCongr σ) x).val = (σ ⟨x.val, by omega⟩).val := by
  subst s
  rfl

/-- 概要：移送した外側交換は次に代入する最後の位置を先頭へ送る（Berger–Moerdijk §1）。
方針：Fin の長さの移送は値を保つことと、残りの位置の計算則を使う。
規約：位置は a とする。
使われ方：二段目の部分合成の代入位置を同定する。 -/
@[simp]
lemma operadTwoSwapAfterFirst_last (a : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapAfterFirst a ⟨a, by omega⟩ = 0 := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapAfterFirst, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
  exact congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwap_remaining a)

/-- 概要：移送した外側交換は最初のブロック内の各位置を一つ後ろへ送る（Berger–Moerdijk §1）。
方針：長さの移送は値を保つことと、挿入区間の計算則を使う。
規約：ブロック内の位置は Fin a で表す。
使われ方：二段目の代入後の出力のブロック交換を計算する。 -/
lemma operadTwoSwapAfterFirst_prefix (a : ℕ) (j : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapAfterFirst a ⟨j.val, by omega⟩ = ⟨1 + j.val, by omega⟩ := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapAfterFirst, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
  exact congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwap_inserted a j)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
