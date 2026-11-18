module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TailBlockSwap

/-!
模型。文献の定義との比較は後で
# 二ブロック交換の値

概要：Berger–Moerdijk §1 の外側等変性の出力を自然数の位置で計算する。
方針：前方、左ブロック、右ブロック、後方の四区間の既存の計算をまとめる。
規約：各ブロックの内部の順序を保ち、長さ零も許す。
使われ方：異なる再帰で定義された隣接ブロック交換を点ごとに比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：中央の二ブロック交換の値を四区間の条件式で表す（Berger–Moerdijk §1）。
方針：各区間の入力を対応する標準有限集合の元として表し、既存の計算則を適用する。
規約：前方 p 個と後方 q 個は固定する。
使われ方：反復合成とテンソル族の出力の全単射を値で比較する。 -/
lemma operadContextBlockSwap_val (p q a b : ℕ) (x : Fin (((p + q) + a) + b)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap p q a b x).val =
      if x.val < p then x.val else
      if x.val < p + a then x.val + b else
      if x.val < p + a + b then x.val - a else x.val := by
  by_cases h₀ : x.val < p
  · let z : Fin p := ⟨x.val, h₀⟩
    have hx : (⟨z.val, by omega⟩ : Fin (((p + q) + a) + b)) = x := by
      apply Fin.ext; rfl
    have h := congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_before p q a b z)
    rw [hx] at h
    simpa only [ite_eq_left h₀] using h
  · by_cases h₁ : x.val < p + a
    · let z : Fin a := ⟨x.val - p, by omega⟩
      have hx : (⟨p + z.val, by omega⟩ : Fin (((p + q) + a) + b)) = x := by
        apply Fin.ext; dsimp [z]; omega
      have h := congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_left p q a b z)
      rw [hx] at h
      simp only [ite_eq_right h₀, ite_eq_left h₁]
      dsimp [z] at h
      omega
    · by_cases h₂ : x.val < p + a + b
      · let z : Fin b := ⟨x.val - (p + a), by omega⟩
        have hx : (⟨p + a + z.val, by omega⟩ : Fin (((p + q) + a) + b)) = x := by
          apply Fin.ext; dsimp [z]; omega
        have h := congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_right p q a b z)
        rw [hx] at h
        simp only [ite_eq_right h₀, ite_eq_right h₁, ite_eq_left h₂]
        dsimp [z] at h
        omega
      · let z : Fin q := ⟨x.val - (p + a + b), by omega⟩
        have hx : (⟨p + a + b + z.val, by omega⟩ : Fin (((p + q) + a) + b)) = x := by
          apply Fin.ext; dsimp [z]; omega
        have h := congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_after p q a b z)
        rw [hx] at h
        simp only [ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂]
        dsimp [z] at h
        omega

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
