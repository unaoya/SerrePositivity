module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordMap
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterCategory
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordRetractionAction

/-!
# 中断した任意モデル源への一般化：WordPresentationRealization

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual degreewise evaluation of the word presentation from strong contractions。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0612][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0612
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual degreewise evaluation of the word presentation from strong contractions

Every defining relation is checked using the actual word action. No model
structure, additional coherence witness, or evaluation-kernel quotient is used.
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.WordPresentationRealization

def parameterEvaluation {T : SSet.{v}} (n : SimplexCategoryᵒᵖ) (t : T.obj n) :
    ParameterCategory.Object T ⥤ Type v where
  obj X := X.value.obj n
  map f := ↾fun x => f.app n (x, t)
  map_id _ := rfl
  map_comp _ _ := rfl

variable {C : Type u} [Category.{w} C] {T : SSet.{v}}
  (F : C ⥤ ParameterCategory.Object T) (K : C → SSet.{v})
  (s : ∀ X, K X ⟶ (F.obj X).value) (p : ∀ X, (F.obj X).value ⟶ K X)
  (hs : ∀ X, s X ≫ p X = 𝟙 (K X))
  (H : ∀ X, SSet.Homotopy (𝟙 (F.obj X).value) (p X ≫ s X))
  (hP : ∀ X, (H X).h ≫ p X = fst (F.obj X).value WordSegment.interval ≫ p X)
  (hS : ∀ X, s X ▷ WordSegment.interval ≫ (H X).h = fst (K X) WordSegment.interval ≫ s X)

def realization (n : SimplexCategoryᵒᵖ) (t : T.obj n) :
    RetractWords.Realization C (WordSegment.degree n) (Type v) where
  ambient := F ⋙ parameterEvaluation n t
  small X := (K X).obj n
  section_ X := (s X).app n
  projection X := (p X).app n
  action X w := ↾fun x => WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n w x
  action_one X := by
    apply ConcreteCategory.hom_ext
    intro x
    change WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n 1 x = x
    rw [map_one, RetractEndomorphisms.one_apply]
  action_mul X a b := by
    apply ConcreteCategory.hom_ext
    intro x
    change WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n (a * b) x = _
    rw [map_mul]
    rfl
  split X := congr_app (hs X) n
  action_zero X := by
    apply ConcreteCategory.hom_ext
    intro x
    change WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n 0 x = _
    rw [map_zero, RetractEndomorphisms.zero_apply]
    rfl
  section_action X w := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n w).fixed x
  action_projection X w := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n w).over x

abbrev functor (n : SimplexCategoryᵒᵖ) (t : T.obj n) :=
  (realization F K s p hs H hP hS n t).functor

abbrev smallFunctor (n : SimplexCategoryᵒᵖ) (t : T.obj n) :=
  (realization F K s p hs H hP hS n t).smallFunctor

end SerrePositivity.SimplicialModel.WordPresentationRealization
