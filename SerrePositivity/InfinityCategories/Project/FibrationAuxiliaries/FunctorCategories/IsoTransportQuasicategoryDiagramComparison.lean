module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTransportQuasicategoryComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedOrdinaryNaturality
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison

/-!
概要：指定同型の全局所 Hom に自然な比較を、底全体の図式の比較へ束ねる。
方針：底の各豊穣比較の通常の射に対する自然性を、その同じ指定同型へ適用する。
規約：元の比較成分と全高次 Hom の作用を保持する。
使われ方：結合共役の分類像を底全体の同じ結合 Hom 輸送と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 同じ指定同型の二つの評価は、全高次 Hom と底全体の射に自然な比較を持つ。 -/
def isoTransportQuasicategoryDiagramComparison
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison
      (D.precompose (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isoTransportSourceEnriched SSet.{u} C))
      (D.precompose (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isoTransportTargetEnriched SSet.{u} C)) where
  app j := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isoTransportQuasicategoryComparison (D.obj j)
  naturality f X :=
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedComparison_ordinary_naturality (D.map f) X.comparison.hom).symm

/-- 同じ底全体の比較の各成分は、指定同型の元の関手像として同値。 -/
lemma isoTransportQuasicategoryDiagramComparison_component_isQCatEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J)
    (j : J) (X : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTransportObject C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((isoTransportQuasicategoryDiagramComparison D).app j |>.val X) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isoTransportQuasicategoryComparison_component_isQCatEquivalence (D.obj j) X

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
