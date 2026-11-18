module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.BinarySlotSwap

/-!
模型。文献の定義との比較は後で
# 二段の外側等変性の出力とブロック交換

概要：Berger–Moerdijk §1 の二入力の外側交換を、代入後の二ブロックの交換として同定する。
方針：二段目の挿入区間と残りの入力で外側置換を計算する。
規約：出力の arity の式は Fin の標準同値で移送する。
使われ方：二入力の合成の外側等変性の係数側の出力を記述する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：二段目の代入に外側交換を延長した出力の置換（Berger–Moerdijk §1）。
方針：最初の代入後の外側交換を、位置 a への二番目の代入へ延長する。
規約：出力の arity の式は 0+a+b。
使われ方：二入力の外側等変性で得られる出力の置換となる。 -/
def operadTwoSwapOutput (a b : ℕ) : Equiv.Perm (Fin ((0 + a) + b)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (0 + a) b ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapAfterFirst a)

/-- 概要：二番目に代入した入力ブロックは出力の先頭へ移る（Berger–Moerdijk §1）。
方針：外側置換の挿入区間内の計算則と、代入位置の移動を用いる。
規約：ブロック内の順序は変わらない。
使われ方：二段の外側等変性の出力を右ブロックの入力で計算する。 -/
lemma operadTwoSwapOutput_inserted (a b : ℕ) (j : Fin b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapOutput a b ⟨a + j.val, by omega⟩ = ⟨j.val, by omega⟩ := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_inside (0 + a) b ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapAfterFirst a) j
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapAfterFirst_last, Fin.val_zero, Nat.zero_add] at h
  exact h

/-- 概要：最初に代入した入力ブロックは出力の後方へ移る（Berger–Moerdijk §1）。
方針：挿入分解の残りの入力を評価し、最初の外側交換の位置の計算則を用いる。
規約：ブロック内の順序は変わらない。
使われ方：二段の外側等変性の出力を左ブロックの入力で計算する。 -/
lemma operadTwoSwapOutput_prefix (a b : ℕ) (j : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapOutput a b ⟨j.val, by omega⟩ = ⟨b + j.val, by omega⟩ := by
  have hj : j.val < a := j.isLt
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapAfterFirst_prefix a j
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapOutput, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv, hj, hp, -Fin.val_fin_lt]
  omega

/-- 概要：二段の外側等変性の出力を標準の二つの総 arity の間へ移す（Berger–Moerdijk §1）。
方針：入力を a+b から再帰の 0+a+b へ移し、出力を b+a へ移す。
規約：移送は入力の自然数の値を保つ。
使われ方：対称列の有限全単射の作用に適用する出力の全単射となる。 -/
def operadBinaryOutputSwap (a b : ℕ) : Fin (a + b) ≃ Fin (b + a) :=
  (finCongr (by omega : a + b = (0 + a) + b)).trans
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapOutput a b).trans (finCongr (by omega : (0 + a) + b = b + a)))

/-- 概要：二段の外側等変性の出力は標準の二ブロックの交換である（Berger–Moerdijk §1）。
方針：有限直和の左右の入力に分け、それぞれの位置の計算則を使う。
規約：零長のブロックも許す。
使われ方：二入力の全合成の外側等変性の出力をブロック交換として読む。 -/
lemma operadBinaryOutputSwap_eq (a b : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBinaryOutputSwap a b = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl x =>
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBinaryOutputSwap a b (x.castAdd b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b (x.castAdd b)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left]
    apply Fin.ext
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapOutput a b ⟨x.val, by omega⟩).val = (x.natAdd b).val
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapOutput_prefix]
    rfl
  | inr x =>
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBinaryOutputSwap a b (x.natAdd a) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b (x.natAdd a)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right]
    apply Fin.ext
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapOutput a b ⟨a + x.val, by omega⟩).val = (x.castAdd a).val
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSwapOutput_inserted]
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
