module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 中断した任意モデル源への一般化：SimplexChainParameter

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual first-vertex parameter of a chain of simplex operators。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0045][inventory]を参照する。

[inventory]: ../../formalization-plans/k-theory-generalization-inventory.md#m0045
[plan]: ../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual first-vertex parameter of a chain of simplex operators

All vertices come from the same first simplex by the actual prefix maps.
Restriction factors through the prefix leading to the new first simplex.
-/

@[expose] public section
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplexChainParameter
variable {n : ℕ} (c : Fin (n + 1) ⥤ SimplexCategoryᵒᵖ)

lemma prefix_comp {i j : Fin (n + 1)} (h : i ≤ j) :
    c.map (homOfLE (Fin.zero_le j)) =
      c.map (homOfLE (Fin.zero_le i)) ≫ c.map (homOfLE h) :=
  c.map_comp _ _

abbrev vertex (i : Fin (n + 1)) : Fin ((c.obj 0).unop.len + 1) :=
  (c.map (homOfLE (Fin.zero_le i))).unop.toOrderHom 0

lemma monotone : Monotone (vertex c) := by
  intro i j h
  have e := congrArg (fun f => f.unop.toOrderHom 0) (prefix_comp c h)
  change vertex c j = (c.map (homOfLE (Fin.zero_le i))).unop.toOrderHom
    ((c.map (homOfLE h)).unop.toOrderHom 0) at e
  rw [e]
  exact (c.map (homOfLE (Fin.zero_le i))).unop.toOrderHom.monotone (Fin.zero_le _)

def parameter : SimplexCategory.mk n ⟶ (c.obj 0).unop :=
  SimplexCategory.Hom.mk ⟨vertex c, monotone c⟩

lemma parameter_apply (i : Fin (n + 1)) :
    (parameter c).toOrderHom i = vertex c i := rfl

lemma parameter_zero : (parameter c).toOrderHom 0 = 0 := by
  change (c.map (𝟙 0)).unop.toOrderHom 0 = 0
  rw [c.map_id]
  rfl

lemma reindex {m : ℕ} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    θ ≫ parameter c =
      parameter ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).unop := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  exact congrArg (fun f => f.unop.toOrderHom 0)
    (prefix_comp c (θ.toOrderHom.monotone (Fin.zero_le i)))

end SerrePositivity.SimplexChainParameter
