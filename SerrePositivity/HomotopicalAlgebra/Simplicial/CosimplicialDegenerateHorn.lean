module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.DegenerateHornInput
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# 中断した任意モデル源への一般化：CosimplicialDegenerateHorn

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Degenerate maps with the same horn agree for any cosimplicial object。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0375][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0375
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Degenerate maps with the same horn agree for any cosimplicial object

For distinct degeneracies, one visible face forces one map to factor
through the other degeneracy as well. A visible section face then gives
the equality. The argument uses only cosimplicial identities, in an
arbitrary category; no model structure or Kan condition is involved.
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.CosimplicialDegenerateHorn
variable {C : Type u} [Category.{v} C] (X : CosimplicialObject C) {P : C}

private lemma section_face {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    X.δ (DegenerateHornInput.visibleFace i j) ≫ X.σ j = 𝟙 _ := by
  by_cases h : j.castSucc ≠ i
  · simp only [DegenerateHornInput.visibleFace, ite_eq_left h]
    exact X.δ_comp_σ_self
  · simp only [DegenerateHornInput.visibleFace, ite_eq_right h]
    exact X.δ_comp_σ_succ

private lemma same_degeneracy {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (a b : X.obj (SimplexCategory.mk n) ⟶ P)
    (h : ∀ r : Fin (n + 2), r ≠ i → X.δ r ≫ X.σ j ≫ a = X.δ r ≫ X.σ j ≫ b) : a = b := by
  have he := h (DegenerateHornInput.visibleFace i j) (DegenerateHornInput.visibleFace_ne i j)
  simpa only [← Category.assoc, section_face X i j, Category.id_comp] using he

private lemma ordered {n : ℕ} (i : Fin (n + 2)) (j k : Fin (n + 1)) (hjk : j < k)
    (a b : X.obj (SimplexCategory.mk n) ⟶ P)
    (h : ∀ r : Fin (n + 2), r ≠ i → X.δ r ≫ X.σ j ≫ a = X.δ r ≫ X.σ k ≫ b) :
    X.σ j ≫ a = X.σ k ≫ b := by
  cases n with
  | zero =>
    have hj := j.isLt
    have hk := k.isLt
    have hlt : j.val < k.val := hjk
    omega
  | succ n =>
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    have hjk' : j ≤ k := by
      have hlt : j.val < k.val + 1 := hjk
      omega
    by_cases hi : j.castSucc.castSucc ≠ i
    · have hf := h j.castSucc.castSucc hi
      have hδ : X.δ j.castSucc.castSucc ≫ X.σ k.succ = X.σ k ≫ X.δ j.castSucc :=
        X.δ_comp_σ_of_le (by simpa only [Fin.castSucc_le_castSucc_iff] using hjk')
      have hs : X.δ j.castSucc.castSucc ≫ X.σ j.castSucc = 𝟙 _ := X.δ_comp_σ_self
      have ha : a = X.σ k ≫ X.δ j.castSucc ≫ b := calc
        _ = X.δ j.castSucc.castSucc ≫ X.σ j.castSucc ≫ a := by
          rw [← Category.assoc, hs, Category.id_comp]
        _ = X.δ j.castSucc.castSucc ≫ X.σ k.succ ≫ b := hf
        _ = _ := by rw [← Category.assoc, hδ, Category.assoc]
      let c := X.σ j ≫ X.δ j.castSucc ≫ b
      have he : X.σ j.castSucc ≫ a = X.σ k.succ ≫ c := by
        rw [ha, ← Category.assoc, X.σ_comp_σ hjk', Category.assoc]
      have hc : c = b := same_degeneracy X i k.succ c b (by
        intro r hr
        rw [← he]
        exact h r hr)
      rw [he, hc]
    · have hi' : i = j.castSucc.castSucc := (not_not.mp hi).symm
      have hr : k.succ.succ ≠ i := by
        rw [hi']
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_succ, Fin.val_castSucc] at hv
        omega
      have hf := h k.succ.succ hr
      have hδ : X.δ k.succ.succ ≫ X.σ j.castSucc = X.σ j ≫ X.δ k.succ :=
        X.δ_comp_σ_of_gt (by
          have hlt : j.val < k.val + 1 := hjk
          exact hlt)
      have hs : X.δ k.succ.succ ≫ X.σ k.succ = 𝟙 _ := X.δ_comp_σ_succ
      have hb : b = X.σ j ≫ X.δ k.succ ≫ a := calc
        _ = X.δ k.succ.succ ≫ X.σ k.succ ≫ b := by
          rw [← Category.assoc, hs, Category.id_comp]
        _ = X.δ k.succ.succ ≫ X.σ j.castSucc ≫ a := hf.symm
        _ = _ := by rw [← Category.assoc, hδ, Category.assoc]
      let c := X.σ k ≫ X.δ k.succ ≫ a
      have he : X.σ k.succ ≫ b = X.σ j.castSucc ≫ c := by
        rw [hb, ← Category.assoc, ← X.σ_comp_σ hjk', Category.assoc]
      have hc : a = c := same_degeneracy X i j.castSucc a c (by
        intro r hr
        rw [← he]
        exact h r hr)
      rw [he, hc]

lemma eq_of_faces {n : ℕ} (i : Fin (n + 2)) (j k : Fin (n + 1))
    (a b : X.obj (SimplexCategory.mk n) ⟶ P)
    (h : ∀ r : Fin (n + 2), r ≠ i → X.δ r ≫ X.σ j ≫ a = X.δ r ≫ X.σ k ≫ b) :
    X.σ j ≫ a = X.σ k ≫ b := by
  rcases lt_trichotomy j k with hjk | hjk | hkj
  · exact ordered X i j k hjk a b h
  · subst k
    exact congrArg (fun q => X.σ j ≫ q) (same_degeneracy X i j a b h)
  · exact (ordered X i k j hkj b a (fun r hr => (h r hr).symm)).symm

end SerrePositivity.SimplicialModel.CosimplicialDegenerateHorn
