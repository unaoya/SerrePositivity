module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramRestriction
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：quasicategory 値豊穣図式の比較を、底全体と全高次 Hom に関して束ねる。
方針：各底対象の豊穣比較と、底の全射に関する厳密な自然性を保持する。
規約：同じ対象で評価した比較を、二点と底の積の通常の図式にする。
使われ方：底変換比較を同じ分類主写像の間の一つの coherent な族へ実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 底全体で厳密に自然な、全高次 Hom に自然な豊穣比較の族。 -/
structure QuasicategoryEnrichedDiagramComparison
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) where
  app : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison (D.obj j) (E.obj j)
  naturality : ∀ {i j} (f : i ⟶ j) X,
    (D.map f).val X ≫ (app j).val X = (app i).val X ≫ (E.map f).val X

/-- 元の全対象の一つで評価すると、底の全射に自然な同じ比較となる。 -/
def QuasicategoryEnrichedDiagramComparison.evaluate
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
    (η : QuasicategoryEnrichedDiagramComparison D E) (X : C) : D.evaluate X ⟶ E.evaluate X where
  app j := (η.app j).val X
  naturality i j f := η.naturality f X

/-- 同じ比較の全対象での二点と底の積上の通常の図式。 -/
def QuasicategoryEnrichedDiagramComparison.arrow
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
    (η : QuasicategoryEnrichedDiagramComparison D E) (X : C) :
    Fin 2 × J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} :=
  CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ (η.evaluate X))

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
