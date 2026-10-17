module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource
public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationSourceMap

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFixedWordResolution

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual diagonal word resolution with fixed literal base objects。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0170][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0170
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual diagonal word resolution with fixed literal base objects

It is naturally isomorphic to the previously constructed diagonal. Its
small-vertex Hom simplicial sets have the original base as literal labels.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedSource
variable (C : Type u) [Category.{v} C]

def diagram : SimplicialObject Cat.{max u v, u} :=
  WordPresentationAugmentation.diagonal.{u, max u v, max u v} (literal C)

def sourceIso : literal C ≅ OrdinaryBarWordResolution.source C :=
  eqToIso (literal_eq C) ≪≫ comparisonIso C

def comparisonIso : diagram C ≅ OrdinaryBarWordResolution.diagonal C :=
  CategoryTheory.Functor.isoWhiskerLeft (Functor.diag _)
    (Functor.uncurry.mapIso (CategoryTheory.Functor.isoWhiskerRight (sourceIso C)
      (WordPresentationCat.simplicialFunctor.{u, max u v, max u v})))

lemma map_functor {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((diagram C).map θ).toFunctor =
      RetractWords.map (literalMap C θ) (MonoidWithZeroHom.id (WordSegment.degree.{max u v} n)) ⋙
        RetractWords.map (𝟭 (degree (D C) (m.unop.len + 1))) (WordSegment.degreeMap θ) := rfl

lemma map_functor_reverse {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((diagram C).map θ).toFunctor =
      RetractWords.map (𝟭 (degree (D C) (n.unop.len + 1))) (WordSegment.degreeMap θ) ⋙
        RetractWords.map (literalMap C θ)
          (MonoidWithZeroHom.id (WordSegment.degree.{max u v} m)) := by
  rw [map_functor]
  exact WordPresentationSourceMap.commute (literalMap C θ) θ

def hom (X Y : D C) : SSet.{max u v} where
  obj n := (RetractWords.quotient (degree (D C) (n.unop.len + 1))
      (WordSegment.degree.{max u v} n)).obj (.small X) ⟶
    (RetractWords.quotient (degree (D C) (n.unop.len + 1))
      (WordSegment.degree.{max u v} n)).obj (.small Y)
  map θ := ↾fun f => ((diagram C).map θ).toFunctor.map f
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congrArg Cat.Hom.toFunctor ((diagram C).map_id n)
    have hf := congr($(h).map f)
    exact hf
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congrArg Cat.Hom.toFunctor ((diagram C).map_comp θ φ)
    have hf := congr($(h).map f)
    exact hf

open CategoryTheory.MonoidalCategory

def composition (X Y Z : D C) : hom C X Y ⊗ hom C Y Z ⟶ hom C X Z where
  app n := ↾fun f => f.1 ≫ f.2
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    exact (((diagram C).map θ).toFunctor.map_comp f.1 f.2).symm

def identity (X : D C) : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ hom C X X where
  app n := ↾fun _ => 𝟙 _
  naturality {n _} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (((diagram C).map θ).toFunctor.map_id
      ((RetractWords.quotient (degree (D C) (n.unop.len + 1))
        (WordSegment.degree.{max u v} n)).obj (.small X))).symm

lemma composition_assoc (W X Y Z : D C) :
    composition C W X Y ▷ hom C Y Z ≫ composition C W Y Z =
      (α_ (hom C W X) (hom C X Y) (hom C Y Z)).hom ≫
        hom C W X ◁ composition C X Y Z ≫ composition C W X Z := by
  ext n x
  exact Category.assoc x.1.1 x.1.2 x.2

open CategoryTheory.CartesianMonoidalCategory in
lemma identity_left {T : SSet.{max u v}} {X Y : D C} (a : T ⟶ hom C X Y) :
    lift (SSet.stdSimplex.isTerminalObj₀.from T ≫ identity C X) a ≫ composition C X X Y = a := by
  ext n x
  exact Category.id_comp (a.app n x)

open CategoryTheory.CartesianMonoidalCategory in
lemma identity_right {T : SSet.{max u v}} {X Y : D C} (a : T ⟶ hom C X Y) :
    lift a (SSet.stdSimplex.isTerminalObj₀.from T ≫ identity C Y) ≫ composition C X Y Y = a := by
  ext n x
  exact Category.comp_id (a.app n x)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution
