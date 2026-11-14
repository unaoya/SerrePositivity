module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationNaturality
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftFillers

/-!
# 中断した任意モデル源への一般化：WordPresentationAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual simplicial evaluation and parameterized action of the presented word category。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0607][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0607
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual simplicial evaluation and parameterized action of the presented word category

The source and value universes remain independent. Universe lifts are used
only to put tensor factors in a common auxiliary universe; no model is used.
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.WordPresentationAction
open WordPresentationRealization WordPresentationNaturality
variable {C : Type u} [Category.{w} C] {T : SSet.{v}}
  (F : C ⥤ ParameterCategory.Object T) (K : C → SSet.{v})
  (s : ∀ X, K X ⟶ (F.obj X).value) (p : ∀ X, (F.obj X).value ⟶ K X)
  (hs : ∀ X, s X ≫ p X = 𝟙 (K X))
  (H : ∀ X, SSet.Homotopy (𝟙 (F.obj X).value) (p X ≫ s X))
  (hP : ∀ X, (H X).h ≫ p X = fst (F.obj X).value WordSegment.interval ≫ p X)
  (hS : ∀ X, s X ▷ WordSegment.interval ≫ (H X).h = fst (K X) WordSegment.interval ≫ s X)

def action (X Y : C) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u w v} (K X) ⊗
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u w v} T ⊗ WordPresentationDiagram.smallHom.{u, w, v} C X Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u w v} (K Y) where
  app n := ↾fun x => ULift.up ((R F K s p hs H hP hS n x.2.1.down).functor.map x.2.2 x.1.down)
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up
      (small_naturality F K s p hs H hP hS θ x.2.1.down X Y x.2.2 x.1.down).symm

def family {U : SSet.{max u w v}} (X Y : C)
    (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u w v} T)
    (f : U ⟶ WordPresentationDiagram.smallHom.{u, w, v} C X Y) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u w v} (K X) ⊗ U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u w v} (K Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj (K X) ◁ lift t f ≫ action F K s p hs H hP hS X Y

lemma family_substitute {U V : SSet.{max u w v}} (X Y : C)
    (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u w v} T)
    (f : U ⟶ WordPresentationDiagram.smallHom.{u, w, v} C X Y) (j : V ⟶ U) :
    family F K s p hs H hP hS X Y (j ≫ t) (j ≫ f) =
      ParameterComposition.substitute j (family F K s p hs H hP hS X Y t f) := by
  ext n x
  rfl

lemma family_identity {U : SSet.{max u w v}} (X : C)
    (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u w v} T) :
    family F K s p hs H hP hS X X t
      (SSet.stdSimplex.isTerminalObj₀.from U ≫ WordPresentationDiagram.identity C X) =
      fst (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj (K X)) U := by
  ext n x
  change ULift.up ((R F K s p hs H hP hS n (t.app n x.2).down).functor.map
    (𝟙 ((RetractWords.quotient C (WordSegment.degree.{v} n)).obj (.small X))) x.1.down) = x.1
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma family_comp {U : SSet.{max u w v}} (X Y Z : C)
    (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u w v} T)
    (f : U ⟶ WordPresentationDiagram.smallHom.{u, w, v} C X Y)
    (g : U ⟶ WordPresentationDiagram.smallHom.{u, w, v} C Y Z) :
    ParameterComposition.comp (family F K s p hs H hP hS X Y t f)
        (family F K s p hs H hP hS Y Z t g) =
      family F K s p hs H hP hS X Z t (lift f g ≫ WordPresentationDiagram.composition C X Y Z) := by
  ext n x
  change _ = ULift.up ((R F K s p hs H hP hS n (t.app n x.2).down).functor.map
    (f.app n x.2 ≫ g.app n x.2) x.1.down)
  rw [CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.SimplicialModel.WordPresentationAction
