module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexParameterHom

/-!
# 中断した任意モデル源への一般化：ParameterComposition

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Composition with one arbitrary shared simplicial parameter。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0509][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0509
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Composition with one arbitrary shared simplicial parameter

The same parameter is retained at each stage of composition. Substitution
of the entire parameter commutes with composition as an actual equality.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.ParameterComposition
variable {T U X Y Z W : SSet.{v}}

def comp (f : X ⊗ T ⟶ Y) (g : Y ⊗ T ⟶ Z) : X ⊗ T ⟶ Z :=
  lift f (snd X T) ≫ g

def const (T : SSet.{v}) (f : X ⟶ Y) : X ⊗ T ⟶ Y := fst X T ≫ f

def substitute (j : U ⟶ T) (f : X ⊗ T ⟶ Y) : X ⊗ U ⟶ Y := X ◁ j ≫ f

lemma assoc (f : X ⊗ T ⟶ Y) (g : Y ⊗ T ⟶ Z) (h : Z ⊗ T ⟶ W) :
    comp (comp f g) h = comp f (comp g h) := by ext n x; rfl

lemma id_comp (f : X ⊗ T ⟶ Y) : comp (const T (𝟙 X)) f = f := by ext n x; rfl

lemma comp_id (f : X ⊗ T ⟶ Y) : comp f (const T (𝟙 Y)) = f := by ext n x; rfl

lemma const_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    comp (const T f) (const T g) = const T (f ≫ g) := by ext n x; rfl

lemma comp_const (f : X ⊗ T ⟶ Y) (g : Y ⟶ Z) :
    comp f (const T g) = f ≫ g := by ext n x; rfl

lemma const_comp_family (f : X ⟶ Y) (g : Y ⊗ T ⟶ Z) :
    comp (const T f) g = f ▷ T ≫ g := by ext n x; rfl

lemma pre_comp {V : SSet.{v}} (i : V ⟶ X)
    (f : X ⊗ T ⟶ Y) (g : Y ⊗ T ⟶ Z) :
    i ▷ T ≫ comp f g = comp (i ▷ T ≫ f) g := by ext n x; rfl

lemma substitute_comp (j : U ⟶ T) (f : X ⊗ T ⟶ Y) (g : Y ⊗ T ⟶ Z) :
    substitute j (comp f g) = comp (substitute j f) (substitute j g) := by ext n x; rfl

lemma substitute_const (j : U ⟶ T) (f : X ⟶ Y) :
    substitute j (const T f) = const U f := by ext n x; rfl

lemma simplex_comp {n : SimplexCategory}
    (f : X ⊗ SSet.stdSimplex.obj n ⟶ Y) (g : Y ⊗ SSet.stdSimplex.obj n ⟶ Z) :
    comp f g = SimplexParameterHom.composeFamily f g := rfl

end SerrePositivity.SimplicialModel.ParameterComposition
