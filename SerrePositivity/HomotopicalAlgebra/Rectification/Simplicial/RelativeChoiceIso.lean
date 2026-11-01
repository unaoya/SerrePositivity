module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceMaps

/-!
# 中断した任意モデル源への一般化：RelativeChoiceIso

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Isomorphisms of actual relative choice spaces。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0539][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0539
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Isomorphisms of actual relative choice spaces

An isomorphism of targets preserving the specified boundary induces an
isomorphism of the actual pullback spaces. Entire parameter families,
including all already specified faces, are transported unchanged.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.RelativeChoiceSpace
variable {V T P Q : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q)
  (e : P ≅ Q) (he : b ≫ e.hom = b')

include he in
lemma boundary_inv : b' ≫ e.inv = b := by
  rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]

def postIso : obj i b ≅ obj i b' where
  hom := postMap i b b' e.hom he
  inv := postMap i b' b e.inv (boundary_inv b b' e he)
  hom_inv_id := by
    rw [postMap_compose]
    simpa only [e.hom_inv_id] using postMap_identity i b
  inv_hom_id := by
    rw [postMap_compose]
    simpa only [e.inv_hom_id] using postMap_identity i b'

@[reassoc (attr := simp)]
lemma postIso_hom_projection : (postIso i b b' e he).hom ≫ projection i b' = projection i b :=
  postMap_projection i b b' e.hom he

@[reassoc (attr := simp)]
lemma postIso_inv_projection : (postIso i b b' e he).inv ≫ projection i b = projection i b' :=
  postMap_projection i b' b e.inv (boundary_inv b b' e he)

lemma family_postIso_hom {K : SSet.{v}} (s : K ⟶ obj i b) :
    family i b' (s ≫ (postIso i b b' e he).hom) = family i b s ≫ e.hom :=
  family_postMap i b b' e.hom he s

lemma family_postIso_inv {K : SSet.{v}} (s : K ⟶ obj i b') :
    family i b (s ≫ (postIso i b b' e he).inv) = family i b' s ≫ e.inv :=
  family_postMap i b' b e.inv (boundary_inv b b' e he) s

lemma postIso_ofExtension (a : T ⟶ P) (ha : i ≫ a = b) :
    ofExtension i b a ha ≫ (postIso i b b' e he).hom =
      ofExtension i b' (a ≫ e.hom) (by rw [← Category.assoc, ha, he]) :=
  postMap_ofExtension i b b' e.hom he a ha

end SerrePositivity.SimplicialModel.RelativeChoiceSpace
