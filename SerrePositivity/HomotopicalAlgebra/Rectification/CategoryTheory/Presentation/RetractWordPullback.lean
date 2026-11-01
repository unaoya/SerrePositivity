module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordMap

/-!
# 中断した任意モデル源への一般化：RetractWordPullback

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Pull back actual realizations along source functors and word homomorphisms。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0028][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0028
[plan]: ../../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Pull back actual realizations along source functors and word homomorphisms
-/

@[expose] public section
universe u v w u' v' w' uD vD
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.RetractWords.Realization
variable {C : Type u} [Category.{v} C] {M : Type w} [MonoidWithZero M]
  {C' : Type u'} [Category.{v'} C'] {N : Type w'} [MonoidWithZero N]
  {D : Type uD} [Category.{vD} D] (R : Realization C M D) (G : C' ⥤ C) (h : N →*₀ M)

def pullback : Realization C' N D where
  ambient := G ⋙ R.ambient
  small X := R.small (G.obj X)
  section_ X := R.section_ (G.obj X)
  projection X := R.projection (G.obj X)
  action X t := R.action (G.obj X) (h t)
  action_one X := by simpa only [map_one, Functor.comp_obj] using R.action_one (G.obj X)
  action_mul X t z := by simpa only [map_mul] using R.action_mul (G.obj X) (h t) (h z)
  split X := R.split (G.obj X)
  action_zero X := by simpa only [map_zero] using R.action_zero (G.obj X)
  section_action X t := R.section_action (G.obj X) (h t)
  action_projection X t := R.action_projection (G.obj X) (h t)

lemma pullback_functor : RetractWords.map G h ⋙ R.functor = (R.pullback G h).functor := by
  apply CategoryTheory.Quotient.lift_unique' (Rel C' N)
  apply Paths.lift_unique (R.pullback G h).edges
  fapply Prefunctor.ext
  · intro X
    cases X <;> rfl
  · intro X Y e
    cases e with
    | source f =>
      change R.functor.map ((RetractWords.map G h).map
        ((quotient C' N).map (source C' N f))) = R.ambient.map (G.map f)
      rw [map_source, R.functor_source]
    | word X t =>
      change R.functor.map ((RetractWords.map G h).map
        ((quotient C' N).map (word C' N X t))) = R.action (G.obj X) (h t)
      rw [map_word, R.functor_word]
    | section_ X =>
      change R.functor.map ((RetractWords.map G h).map
        ((quotient C' N).map (RetractWords.section_ C' N X))) = R.section_ (G.obj X)
      rw [map_section, R.functor_section]
    | projection X =>
      change R.functor.map ((RetractWords.map G h).map
        ((quotient C' N).map (RetractWords.projection C' N X))) = R.projection (G.obj X)
      rw [map_projection, R.functor_projection]

end SerrePositivity.RetractWords.Realization
