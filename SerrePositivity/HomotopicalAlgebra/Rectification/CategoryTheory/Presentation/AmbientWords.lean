module

public import SerrePositivity.CategoryTheory.Quiver.PathFunctorExt
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# 中断した任意モデル源への一般化：AmbientWords

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Source categories with independent monoid actions adjoined at each object。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0023][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/k-theory-generalization-inventory.md#m0023
[plan]: ../../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Source categories with independent monoid actions adjoined at each object

This presentation has only source composition and monoid-action relations.
It contains no formal small vertices or chosen splittings of idempotents.
-/

@[expose] public section
universe u v w uD vD
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.AmbientWords
variable (C : Type u) [Category.{v} C] (M : Type w) [Monoid M]

inductive Vertex (C : Type u) (M : Type w)
  | of : C → Vertex C M

inductive Edge : Vertex C M → Vertex C M → Type (max u v w)
  | source {X Y : C} (f : X ⟶ Y) : Edge (.of X) (.of Y)
  | word (X : C) (t : M) : Edge (.of X) (.of X)

instance : Quiver (Vertex C M) := ⟨Edge C M⟩
abbrev Raw := Paths (Vertex C M)
abbrev source {X Y : C} (f : X ⟶ Y) :
    @Quiver.Path (Vertex C M) (instQuiverVertex C M) (.of X) (.of Y) :=
  (Paths.of (Vertex C M)).map (.source f)
abbrev word (X : C) (t : M) :
    @Quiver.Path (Vertex C M) (instQuiverVertex C M) (.of X) (.of X) :=
  (Paths.of (Vertex C M)).map (.word X t)

inductive Rel : HomRel (Raw C M)
  | source_id (X : C) : Rel (source C M (𝟙 X)) (𝟙 _)
  | source_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
      Rel (source C M f ≫ source C M g) (source C M (f ≫ g))
  | word_one (X : C) : Rel (word C M X 1) (𝟙 _)
  | word_mul (X : C) (t z : M) : Rel (word C M X t ≫ word C M X z) (word C M X (t * z))

abbrev Obj := CategoryTheory.Quotient (Rel C M)
abbrev quotient : Raw C M ⥤ Obj C M := CategoryTheory.Quotient.functor (Rel C M)

lemma word_one (X : C) : (quotient C M).map (word C M X 1) = 𝟙 _ := by
  simpa using CategoryTheory.Quotient.sound (Rel C M) (Rel.word_one X)

lemma word_mul (X : C) (t z : M) :
    (quotient C M).map (word C M X (t * z)) =
      (quotient C M).map (word C M X t) ≫ (quotient C M).map (word C M X z) := by
  simpa using (CategoryTheory.Quotient.sound (Rel C M) (Rel.word_mul X t z)).symm

def sourceFunctor : C ⥤ Obj C M where
  obj X := (quotient C M).obj (Vertex.of X)
  map f := (quotient C M).map (source C M f)
  map_id X := by
    simpa using CategoryTheory.Quotient.sound (Rel C M) (Rel.source_id X)
  map_comp f g := by
    simpa using (CategoryTheory.Quotient.sound (Rel C M) (Rel.source_comp f g)).symm

variable (D : Type uD) [Category.{vD} D]
structure Realization where
  ambient : C ⥤ D
  action : ∀ X, M → (ambient.obj X ⟶ ambient.obj X)
  action_one : ∀ X, action X 1 = 𝟙 _
  action_mul : ∀ X t z, action X (t * z) = action X t ≫ action X z

namespace Realization
variable {C M D} (R : Realization C M D)

def edges : Vertex C M ⥤q D where
  obj | .of X => R.ambient.obj X
  map | .source f => R.ambient.map f | .word X t => R.action X t

abbrev raw : Raw C M ⥤ D := Paths.lift R.edges

lemma respects {X Y : Raw C M} {f g : X ⟶ Y} (h : Rel C M f g) :
    R.raw.map f = R.raw.map g := by
  cases h <;>
    simp only [raw, Functor.map_comp, Functor.map_id, source, word,
      Paths.of_map, Paths.lift_toPath] <;>
    dsimp [edges, Paths.lift] <;> simp [R.action_one, R.action_mul]

def functor : Obj C M ⥤ D :=
  CategoryTheory.Quotient.lift (Rel C M) R.raw (fun _ _ _ _ h => R.respects h)

lemma functor_source {X Y : C} (f : X ⟶ Y) :
    R.functor.map ((quotient C M).map (source C M f)) = R.ambient.map f :=
  Paths.lift_toPath R.edges (Edge.source f)

lemma functor_word (X : C) (t : M) :
    R.functor.map ((quotient C M).map (word C M X t)) = R.action X t :=
  Paths.lift_toPath R.edges (Edge.word X t)

end Realization

lemma functor_ext_generators {D : Type uD} [Category.{vD} D] (F G : Obj C M ⥤ D)
    (ho : ∀ X, F.obj X = G.obj X)
    (hm : ∀ {X Y : Vertex C M} (e : X ⟶ Y),
      HEq (F.map ((quotient C M).map ((Paths.of _).map e)))
        (G.map ((quotient C M).map ((Paths.of _).map e)))) : F = G := by
  apply CategoryTheory.Quotient.lift_unique' (Rel C M)
  apply QuiverPaths.functor_ext_edges
  · intro X
    exact ho ((quotient C M).obj X)
  · intro X Y e
    exact hm e

end SerrePositivity.AmbientWords
