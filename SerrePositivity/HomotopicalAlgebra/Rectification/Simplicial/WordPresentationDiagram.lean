module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordMap
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordSegment
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Category.Cat

/-!
# 中断した任意モデル源への一般化：WordPresentationDiagram

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual simplicial diagram of presented word categories。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0610][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0610
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual simplicial diagram of presented word categories
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.WordPresentationDiagram

lemma degreeMap_id (n : SimplexCategoryᵒᵖ) : WordSegment.degreeMap.{w} (𝟙 n) =
    MonoidWithZeroHom.id (WordSegment.degree n) := by
  apply MonoidWithZeroHom.ext
  intro x
  exact types_congr_hom (WordSegment.obj.map_id n) x

lemma degreeMap_comp {a b c : SimplexCategoryᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    WordSegment.degreeMap.{w} (f ≫ g) =
      (WordSegment.degreeMap g).comp (WordSegment.degreeMap f) := by
  apply MonoidWithZeroHom.ext
  intro x
  exact types_congr_hom (WordSegment.obj.map_comp f g) x

variable (C : Type u) [Category.{v} C]

def diagram : SimplicialObject Cat.{max u v w, u} where
  obj n := Cat.of (RetractWords.Obj C (WordSegment.degree.{w} n))
  map θ := (RetractWords.map (𝟭 C) (WordSegment.degreeMap θ)).toCatHom
  map_id n := by
    apply Cat.Hom.ext
    change RetractWords.map (𝟭 C) (WordSegment.degreeMap (𝟙 n)) = _
    rw [degreeMap_id, RetractWords.map_id]
    rfl
  map_comp f g := by
    apply Cat.Hom.ext
    change RetractWords.map (𝟭 C) (WordSegment.degreeMap (f ≫ g)) =
      RetractWords.map (𝟭 C) (WordSegment.degreeMap f) ⋙
        RetractWords.map (𝟭 C) (WordSegment.degreeMap g)
    rw [degreeMap_comp, ← RetractWords.map_comp, Functor.id_comp]

def smallHom (X Y : C) : SSet.{max u v w} where
  obj n := (RetractWords.quotient C (WordSegment.degree.{w} n)).obj (.small X) ⟶
    (RetractWords.quotient C (WordSegment.degree.{w} n)).obj (.small Y)
  map θ := ↾fun f => (RetractWords.map (𝟭 C) (WordSegment.degreeMap θ)).map f
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    change (RetractWords.map (𝟭 C) (WordSegment.degreeMap (𝟙 n))).map f = f
    rw [degreeMap_id]
    have h := congr($(RetractWords.map_id (C := C) (M := WordSegment.degree.{w} n)).map f)
    exact h
  map_comp {a b c} θ φ := by
    apply ConcreteCategory.hom_ext
    intro f
    change (RetractWords.map (𝟭 C) (WordSegment.degreeMap (θ ≫ φ))).map f =
      (RetractWords.map (𝟭 C) (WordSegment.degreeMap φ)).map
        ((RetractWords.map (𝟭 C) (WordSegment.degreeMap θ)).map f)
    rw [degreeMap_comp]
    have h := congr($(RetractWords.map_comp (𝟭 C) (𝟭 C)
      (WordSegment.degreeMap.{w} θ) (WordSegment.degreeMap φ)).map f)
    simpa only [Functor.id_comp, Functor.comp_map] using h

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory in
def composition (X Y Z : C) : smallHom.{u, v, w} C X Y ⊗ smallHom C Y Z ⟶ smallHom C X Z where
  app n := ↾fun f => f.1 ≫ f.2
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    exact ((RetractWords.map (𝟭 C) (WordSegment.degreeMap θ)).map_comp f.1 f.2).symm

def identity (X : C) : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ smallHom.{u, v, w} C X X where
  app n := ↾fun _ => 𝟙 _
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ((RetractWords.map (𝟭 C) (WordSegment.degreeMap θ)).map_id
      ((RetractWords.quotient C _).obj (.small X))).symm

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

lemma composition_assoc (W X Y Z : C) :
    composition.{u, v, w} C W X Y ▷ smallHom C Y Z ≫ composition C W Y Z =
      (α_ (smallHom C W X) (smallHom C X Y) (smallHom C Y Z)).hom ≫
        smallHom C W X ◁ composition C X Y Z ≫ composition C W X Z := by
  ext n x
  exact Category.assoc x.1.1 x.1.2 x.2

lemma identity_left {T : SSet.{max u v w}} {X Y : C} (a : T ⟶ smallHom.{u, v, w} C X Y) :
    lift (SSet.stdSimplex.isTerminalObj₀.from T ≫ identity C X) a ≫ composition C X X Y = a := by
  ext n x
  exact Category.id_comp (a.app n x)

lemma identity_right {T : SSet.{max u v w}} {X Y : C} (a : T ⟶ smallHom.{u, v, w} C X Y) :
    lift a (SSet.stdSimplex.isTerminalObj₀.from T ≫ identity C Y) ≫ composition C X Y Y = a := by
  ext n x
  exact Category.comp_id (a.app n x)

end SerrePositivity.SimplicialModel.WordPresentationDiagram
