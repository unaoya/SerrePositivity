module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

public import SerrePositivity.CategoryTheory.ArrowFactorization

/-!
# 中断した任意モデル源への一般化：AnchoredChain

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Composable chains with fixed external endpoints。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0001][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0001
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Composable chains with fixed external endpoints

The arrows before and after a finite diagram retain the external endpoints
when an ordinal map omits or repeats diagram vertices. Every cut is an
actual factorization of the same fixed arrow. No model structure is used.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity

structure AnchoredChain {D : Type u} [Category.{v} D] {Y V : D} (g : Y ⟶ V) (n : ℕ) where
  diagram : Fin (n + 1) ⥤ D
  left : Y ⟶ diagram.obj 0
  right : diagram.obj (Fin.last n) ⟶ V
  fac : (left ≫ diagram.map (homOfLE (Fin.zero_le (Fin.last n)))) ≫ right = g

namespace AnchoredChain
variable {D : Type u} [Category.{v} D] {Y V : D} {g : Y ⟶ V} {n m : ℕ}
  (c : AnchoredChain g n)

/-- An ordinary finite composition chain has identity surrounding arrows. -/
def ofDiagram (F : Fin (n + 1) ⥤ D) :
    AnchoredChain (F.map (homOfLE (Fin.zero_le (Fin.last n)))) n where
  diagram := F
  left := 𝟙 _
  right := 𝟙 _
  fac := by simp

abbrev before (k : Fin (n + 1)) : Y ⟶ c.diagram.obj k :=
  c.left ≫ c.diagram.map (homOfLE (Fin.zero_le k))

abbrev after (k : Fin (n + 1)) : c.diagram.obj k ⟶ V :=
  c.diagram.map (homOfLE (Fin.le_last k)) ≫ c.right

lemma before_after (k : Fin (n + 1)) : before c k ≫ after c k = g := by
  calc
    _ = (c.left ≫ (c.diagram.map (homOfLE (Fin.zero_le k)) ≫
        c.diagram.map (homOfLE (Fin.le_last k)))) ≫ c.right := by simp only [Category.assoc]
    _ = (c.left ≫ c.diagram.map (homOfLE (Fin.zero_le (Fin.last n)))) ≫ c.right := by
      rw [← c.diagram.map_comp]
      rfl
    _ = g := c.fac

def cut (k : Fin (n + 1)) : ArrowFactorization g where
  middle := c.diagram.obj k
  left := before c k
  right := after c k
  fac := before_after c k

/-- Reindex the internal diagram and absorb omitted endpoints into the surrounding arrows. -/
def reindex (θ : Fin (m + 1) →o Fin (n + 1)) : AnchoredChain g m where
  diagram := θ.monotone.functor ⋙ c.diagram
  left := c.left ≫ c.diagram.map (homOfLE (Fin.zero_le (θ 0)))
  right := c.diagram.map (homOfLE (Fin.le_last (θ (Fin.last m)))) ≫ c.right
  fac := by
    change ((c.left ≫ c.diagram.map _) ≫ c.diagram.map _) ≫
      (c.diagram.map _ ≫ c.right) = g
    calc
      _ = (c.left ≫ ((c.diagram.map (homOfLE (Fin.zero_le (θ 0))) ≫
          c.diagram.map (θ.monotone.functor.map (homOfLE (Fin.zero_le (Fin.last m))))) ≫
          c.diagram.map (homOfLE (Fin.le_last (θ (Fin.last m)))))) ≫ c.right := by
        simp only [Category.assoc]
      _ = (c.left ≫ c.diagram.map (homOfLE (Fin.zero_le (Fin.last n)))) ≫ c.right := by
        rw [← c.diagram.map_comp, ← c.diagram.map_comp]
        rfl
      _ = g := c.fac

lemma reindex_id : reindex c (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) = c := by
  cases c with
  | mk F a b h =>
    unfold reindex
    congr 1 <;> simp

lemma reindex_comp {l : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    (φ : Fin (l + 1) →o Fin (m + 1)) :
    reindex (reindex c θ) φ = reindex c (θ.comp φ) := by
  cases c with
  | mk F a b h =>
    unfold reindex
    congr 1
    · change (a ≫ F.map _) ≫ F.map _ = a ≫ F.map _
      rw [Category.assoc, ← F.map_comp]
      rfl
    · change F.map _ ≫ (F.map _ ≫ b) = F.map _ ≫ b
      rw [← Category.assoc, ← F.map_comp]
      rfl

lemma before_reindex (θ : Fin (m + 1) →o Fin (n + 1)) (k : Fin (m + 1)) :
    before (reindex c θ) k = before c (θ k) := by
  change (c.left ≫ c.diagram.map _) ≫ c.diagram.map _ = c.left ≫ c.diagram.map _
  rw [Category.assoc, ← c.diagram.map_comp]
  rfl

lemma after_reindex (θ : Fin (m + 1) →o Fin (n + 1)) (k : Fin (m + 1)) :
    after (reindex c θ) k = after c (θ k) := by
  change c.diagram.map _ ≫ (c.diagram.map _ ≫ c.right) = c.diagram.map _ ≫ c.right
  rw [← Category.assoc, ← c.diagram.map_comp]
  rfl

/-- All cuts, including those at omitted endpoints, are preserved as actual factorizations. -/
lemma cut_reindex (θ : Fin (m + 1) →o Fin (n + 1)) (k : Fin (m + 1)) :
    cut (reindex c θ) k = cut c (θ k) := by
  unfold cut
  congr 1
  · exact before_reindex c θ k
  · exact after_reindex c θ k

lemma cut_reindex_id (k : Fin (n + 1)) :
    cut (reindex c (OrderHom.id : Fin (n + 1) →o Fin (n + 1))) k = cut c k :=
  cut_reindex c _ k

lemma cut_reindex_comp {l : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    (φ : Fin (l + 1) →o Fin (m + 1)) (k : Fin (l + 1)) :
    cut (reindex (reindex c θ) φ) k = cut (reindex c (θ.comp φ)) k :=
  (cut_reindex (reindex c θ) φ k).trans
    ((cut_reindex c θ (φ k)).trans (cut_reindex c (θ.comp φ) k).symm)

end AnchoredChain
end SerrePositivity
