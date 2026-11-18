module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AdjacentSlotOutput
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ContextBlockSwap

/-!
模型。文献の定義との比較は後で
# 隣接入力の外側交換の出力と二ブロック交換

概要：Berger–Moerdijk §1 の二位置への合成の外側等変性の出力を標準の二ブロック交換と同定する。
方針：前方、左ブロック、右ブロック、後方の四区間に分けて位置を比較する。
規約：前後の入力と各ブロックの内部の順序を保ち、零長のブロックも許す。
使われ方：反復合成の末尾二入力の交換の出力を、内側ブロックの交換として扱う。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：隣接二入力の外側交換の出力は前後を固定する二ブロック交換である（Berger–Moerdijk §1）。
方針：四つの入力区間で、それぞれの位置の計算則を比較する。
規約：入力の総長は p+q+a+b、出力は p+q+b+a。
使われ方：二位置への合成の出力の全単射をテンソル冪のブロック交換へ接続する。 -/
lemma operadAdjacentSlotOutput_eq_blockSwap (p q a b : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotOutput p q a b = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap p q a b := by
  apply Equiv.ext
  intro x
  by_cases h₀ : x.val < p
  · let z : Fin p := ⟨x.val, h₀⟩
    have hx : (⟨z.val, by omega⟩ : Fin (((p + q) + a) + b)) = x := by apply Fin.ext; rfl
    rw [← hx]
    apply Fin.ext
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond p q a b ⟨z.val, by omega⟩).val = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond_before, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_before]
  · by_cases h₁ : x.val < p + a
    · let z : Fin a := ⟨x.val - p, by omega⟩
      have hx : (⟨p + z.val, by omega⟩ : Fin (((p + q) + a) + b)) = x := by
        apply Fin.ext; dsimp [z]; omega
      rw [← hx]
      apply Fin.ext
      change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond p q a b ⟨p + z.val, by omega⟩).val = _
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_left]
    · by_cases h₂ : x.val < p + a + b
      · let z : Fin b := ⟨x.val - (p + a), by omega⟩
        have hx : (⟨p + a + z.val, by omega⟩ : Fin (((p + q) + a) + b)) = x := by
          apply Fin.ext; dsimp [z]; omega
        rw [← hx]
        apply Fin.ext
        change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond p q a b ⟨p + a + z.val, by omega⟩).val = _
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_right]
      · let z : Fin q := ⟨x.val - (p + a + b), by omega⟩
        have hx : (⟨p + a + b + z.val, by omega⟩ : Fin (((p + q) + a) + b)) = x := by
          apply Fin.ext; dsimp [z]; omega
        rw [← hx]
        apply Fin.ext
        change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond p q a b ⟨p + a + b + z.val, by omega⟩).val = _
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentSlotSecond_after, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_after]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
