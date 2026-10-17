module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWords

/-!
# 中断した任意モデル源への一般化：RetractWordRealization

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Evaluate the retract-word presentation in any category。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0029][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/k-theory-generalization-inventory.md#m0029
[plan]: ../../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Evaluate the retract-word presentation in any category

The data consist of an actual source functor, split retractions, and a
word action. The eight defining equations give an actual functor out of
the presented category, including its full subcategory of small vertices.
-/

@[expose] public section
universe u v w uD vD
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.RetractWords
variable (C : Type u) [Category.{v} C] (M : Type w) [MonoidWithZero M]
  (D : Type uD) [Category.{vD} D]

structure Realization where
  ambient : C ⥤ D
  small : C → D
  section_ : ∀ X, small X ⟶ ambient.obj X
  projection : ∀ X, ambient.obj X ⟶ small X
  action : ∀ X, M → (ambient.obj X ⟶ ambient.obj X)
  action_one : ∀ X, action X 1 = 𝟙 _
  action_mul : ∀ X t z, action X (t * z) = action X t ≫ action X z
  split : ∀ X, section_ X ≫ projection X = 𝟙 _
  action_zero : ∀ X, action X 0 = projection X ≫ section_ X
  section_action : ∀ X t, section_ X ≫ action X t = section_ X
  action_projection : ∀ X t, action X t ≫ projection X = projection X

namespace Realization
variable {C M D} (R : Realization C M D)

def edges : Vertex C M ⥤q D where
  obj
    | .ambient X => R.ambient.obj X
    | .small X => R.small X
  map
    | .source f => R.ambient.map f
    | .word X t => R.action X t
    | .section_ X => R.section_ X
    | .projection X => R.projection X

abbrev raw : Raw C M ⥤ D := Paths.lift R.edges

lemma respects {X Y : Raw C M} {f g : X ⟶ Y} (h : Rel C M f g) :
    R.raw.map f = R.raw.map g := by
  cases h <;>
    simp only [raw, Functor.map_comp, Functor.map_id, source, word,
      RetractWords.section_, RetractWords.projection,
      Paths.of_map, Paths.lift_toPath] <;>
    dsimp [edges, Paths.lift] <;>
    simp [R.action_one, R.action_mul, R.split, R.action_zero, R.section_action, R.action_projection]

def functor : Obj C M ⥤ D :=
  CategoryTheory.Quotient.lift (Rel C M) R.raw (fun _ _ _ _ h => R.respects h)

def smallFunctor : Small C M ⥤ D := inducedFunctor _ ⋙ R.functor

lemma functor_source {X Y : C} (f : X ⟶ Y) :
    R.functor.map ((quotient C M).map (source C M f)) = R.ambient.map f := by
  exact Paths.lift_toPath R.edges (Edge.source f)

lemma functor_word (X : C) (t : M) :
    R.functor.map ((quotient C M).map (word C M X t)) = R.action X t := by
  exact Paths.lift_toPath R.edges (Edge.word X t)

lemma functor_section (X : C) :
    R.functor.map ((quotient C M).map (RetractWords.section_ C M X)) = R.section_ X := by
  exact Paths.lift_toPath R.edges (Edge.section_ X)

lemma functor_projection (X : C) :
    R.functor.map ((quotient C M).map (RetractWords.projection C M X)) = R.projection X := by
  exact Paths.lift_toPath R.edges (Edge.projection X)

lemma source_functor : sourceFunctor C M ⋙ R.functor = R.ambient := by
  refine CategoryTheory.Functor.ext
    (F := sourceFunctor C M ⋙ R.functor) (G := R.ambient) (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change R.functor.map ((quotient C M).map (source C M f)) = R.ambient.map f
  exact R.functor_source f

end Realization
end SerrePositivity.RetractWords
