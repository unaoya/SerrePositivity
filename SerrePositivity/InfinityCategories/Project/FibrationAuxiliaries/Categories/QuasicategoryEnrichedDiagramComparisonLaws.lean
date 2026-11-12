module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparisonComposition

/-!
概要：元の豊穣図式比較の合成・底の制限・全対象の前合成。
方針：同じ比較成分の作用を保持し、全高次と底の両方の自然性を使う。
規約：実際の合成と実際の制限そのものを与える。
使われ方：元の底変換比較の三辺を持つ図式を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 同じ二つの図式比較を、元の成分の合成で束ねる。 -/
def QuasicategoryEnrichedDiagramComparison.trans
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E F : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E)
    (θ : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison E F) : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D F where
  app j := (η.app j).trans (θ.app j)
  naturality {i j} f X := by
    change (D.map f).val X ≫ ((η.app j).val X ≫ (θ.app j).val X) =
      ((η.app i).val X ≫ (θ.app i).val X) ≫ (F.map f).val X
    rw [← Category.assoc, η.naturality, Category.assoc, θ.naturality, Category.assoc]

/-- 同じ図式比較を底の関手で制限する。 -/
def QuasicategoryEnrichedDiagramComparison.reindex
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J L : Type u} [Category.{u} J] [Category.{u} L]
    {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E)
    (k : L ⥤ J) : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison (D.reindex k) (E.reindex k) where
  app j := η.app (k.obj j)
  naturality f X := η.naturality (k.map f) X

/-- 同じ図式比較を元の豊穣関手で全対象・全高次について前合成する。 -/
def QuasicategoryEnrichedDiagramComparison.precompose
    {C : Type v} {L : Type w} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L] {J : Type u} [Category.{u} J]
    {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E)
    (R : EnrichedFunctor SSet.{u} L C) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison (D.precompose R) (E.precompose R) where
  app j := (η.app j).precompose R
  naturality f X := η.naturality f (R.obj X)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
