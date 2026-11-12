module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCocartesianUnit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StraighteningVertices

/-!
概要：元の Cat∞ 値図式と weighted nerve の同じ分類写像での値を coherent な同型で結ぶ。
方針：taut scaffold の自然変換を QCat 値に束ね、同じ変換の prism を実現する。
規約：対象ごとの同値を独立に選ばず、全図式の実際の比較を使う。
使われ方：Cat∞ 値 straightening の像に strict な図式を実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

/-- 小さい quasicategory の通常の圏から underlying 単体集合の圏への忘却。 -/
def qCatForget : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} ⥤ SSet.{u} where
  obj X := X.obj
  map f := f

/-- underlying 図式の値には元の quasicategory 性がある。 -/
instance qCatForget_diagram_quasicategory {C : Type u} [Category.{u} C]
    (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (c : C) : Quasicategory ((F ⋙ qCatForget).obj c) :=
  (F.obj c).isQuasicategory

/-- 元の QCat 値図式を weighted nerve の cocartesian strict transport へ比較する。 -/
def weightedNerveCocartesianQCatUnit {C : Type u} [Category.{u} C]
    (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportQCatFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (F ⋙ qCatForget)) where
  app c := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCocartesianTransportUnit (F ⋙ qCatForget)).app c
  naturality c d f := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCocartesianTransportUnit (F ⋙ qCatForget)).naturality f

/-- 同じ比較は通常の底の全ての高次を保つ coherent な Cat∞ 値図式の同型。 -/
def weightedNerveCocartesianCoherentUnitIso {C : Type u} [Category.{u} C]
    (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (F ⋙ qCatForget))) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramFunctorIsoOfPointwise (weightedNerveCocartesianQCatUnit F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCocartesianTransportUnit_isQCatEquivalence (F ⋙ qCatForget))

/-- 元の strict 図式は、構成済みの同じ分類写像による weighted nerve の像と同型。 -/
def weightedNerveCocartesianStraighteningVertexIso {C : Type u} [Category.{u} C]
    (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap C).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (F ⋙ qCatForget)))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap_vertex]
  exact weightedNerveCocartesianCoherentUnitIso F

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
