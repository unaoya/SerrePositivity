module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.BlockSwapRecursion

/-!
模型。文献の定義との比較は後で
# 前後の入力を保つ二ブロックの交換

概要：Berger–Moerdijk §1 の隣接する二つの代入ブロックの交換を有限全単射で構成する。
方針：前方と後方には恒等全単射、中央の二ブロックには標準のブロック交換を使う。
規約：前方の長さは p、後方は q、中央の二ブロックの長さは a,b。
使われ方：二回の部分合成後の外側等変性の出力をブロック交換として同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：前方と後方を固定し、中央の二ブロックを交換する（Berger–Moerdijk §1）。
方針：三つのブロックへの分解の移送に、二重のブロック全単射を合成する。
規約：arity の表記は前後の長さの和に内側の長さを加えたものとする。
使われ方：任意の外側 arity の隣接二入力の出力の全単射を表す。 -/
def operadContextBlockSwap (p q a b : ℕ) :
    Fin (((p + q) + a) + b) ≃ Fin (((p + q) + b) + a) :=
  (finCongr (by omega : ((p + q) + a) + b = p + ((a + b) + q))).trans
    ((_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin p))
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b) (Equiv.refl (Fin q)))).trans
        (finCongr (by omega : p + ((b + a) + q) = ((p + q) + b) + a)))

/-- 概要：中央の二ブロックの交換は前方の入力を固定する（Berger–Moerdijk §1）。
方針：外側のブロック全単射の左成分を計算する。
規約：前方の入力は Fin p で指定する。
使われ方：出力の全単射の前方の区間を比較する。 -/
lemma operadContextBlockSwap_before (p q a b : ℕ) (x : Fin p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap p q a b ⟨x.val, by omega⟩ = ⟨x.val, by omega⟩ := by
  have hf : finCongr (by omega : ((p + q) + a) + b = p + ((a + b) + q))
      ⟨x.val, by omega⟩ = x.castAdd ((a + b) + q) := by apply Fin.ext; rfl
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap, Equiv.trans_apply]
  rw [hf, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left]
  apply Fin.ext
  rfl

/-- 概要：中央の左ブロックを右ブロックの後へ移す（Berger–Moerdijk §1）。
方針：外側の右成分、内側の左成分、標準ブロック交換の順に計算する。
規約：左ブロックの内部の順序を保つ。
使われ方：代入後の出力の左ブロックの位置と比較する。 -/
lemma operadContextBlockSwap_left (p q a b : ℕ) (x : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap p q a b ⟨p + x.val, by omega⟩ =
      ⟨p + b + x.val, by omega⟩ := by
  have hf : finCongr (by omega : ((p + q) + a) + b = p + ((a + b) + q))
      ⟨p + x.val, by omega⟩ = ((x.castAdd b).castAdd q).natAdd p := by
    apply Fin.ext; rfl
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap, Equiv.trans_apply]
  rw [hf, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left]
  apply Fin.ext
  dsimp
  omega

/-- 概要：中央の右ブロックを左ブロックの前へ移す（Berger–Moerdijk §1）。
方針：外側の右成分、内側の左成分、標準ブロック交換の順に計算する。
規約：右ブロックの内部の順序を保つ。
使われ方：代入後の出力の右ブロックの位置と比較する。 -/
lemma operadContextBlockSwap_right (p q a b : ℕ) (x : Fin b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap p q a b ⟨p + a + x.val, by omega⟩ =
      ⟨p + x.val, by omega⟩ := by
  have hf : finCongr (by omega : ((p + q) + a) + b = p + ((a + b) + q))
      ⟨p + a + x.val, by omega⟩ = ((x.natAdd a).castAdd q).natAdd p := by
    apply Fin.ext; dsimp; omega
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap, Equiv.trans_apply]
  rw [hf, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right]
  apply Fin.ext
  rfl

/-- 概要：中央の二ブロックの交換は後方の入力を固定する（Berger–Moerdijk §1）。
方針：二重のブロック全単射の右成分を計算する。
規約：終域では中央の長さを b+a の順で記述する。
使われ方：出力の全単射の後方の区間を比較する。 -/
lemma operadContextBlockSwap_after (p q a b : ℕ) (x : Fin q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap p q a b ⟨p + a + b + x.val, by omega⟩ =
      ⟨p + b + a + x.val, by omega⟩ := by
  have hf : finCongr (by omega : ((p + q) + a) + b = p + ((a + b) + q))
      ⟨p + a + b + x.val, by omega⟩ = (x.natAdd (a + b)).natAdd p := by
    apply Fin.ext; dsimp; omega
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap, Equiv.trans_apply]
  rw [hf, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right]
  apply Fin.ext
  dsimp
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
