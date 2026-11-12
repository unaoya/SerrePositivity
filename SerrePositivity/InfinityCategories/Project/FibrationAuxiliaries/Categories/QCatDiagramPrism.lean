module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorEdgeFromPrism
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：通常の quasicategory 値図式の自然変換を coherent な prism に実現する。
方針：二点の通常の図式を uncurry し、区間と底の積の射列を coherent nerve に送る。
規約：元の自然変換を保ち、変換空間の Kan 性を仮定しない。
使われ方：weighted nerve の cocartesian 単位の coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 区間の単体と底の射列を、二点の順序と底の積の射列として表す。 -/
def qCatDiagramPrismBase (C : Type u) [Category.{u} C] :
    (Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 2 × C)) where
  app _ := ↾fun ⟨α, σ⟩ ↦
    ULift.up ((SimplexCategory.toCat.map α.down).toFunctor.prod' σ.down)
  naturality _ _ _ := rfl

/-- 自然変換が定める二点と底の積上の通常の図式。 -/
def qCatDiagramArrow {C : Type u} [Category.{u} C] {F G : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}}
    (η : F ⟶ G) : Fin 2 × C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ η)

/-- 同じ通常の自然変換の coherent な prism。 -/
def qCatDiagramNaturalTransformationPrism {C : Type u} [Category.{u} C]
    {F G : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (η : F ⟶ G) :
    (Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} :=
  qCatDiagramPrismBase C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve (qCatDiagramArrow η)

/-- prism の零端点は元の始域図式の coherent 表示。 -/
lemma qCatDiagramNaturalTransformationPrism_zero {C : Type u} [Category.{u} C]
    {F G : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ qCatDiagramNaturalTransformationPrism η =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _
  congr 1

/-- prism の一端点は元の終域図式の coherent 表示。 -/
lemma qCatDiagramNaturalTransformationPrism_one {C : Type u} [Category.{u} C]
    {F G : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ qCatDiagramNaturalTransformationPrism η =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve G := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _
  congr 1

/-- 通常の自然変換の coherent な辺は同じ二つの図式を結ぶ。 -/
def qCatDiagramNaturalTransformationEdge {C : Type u} [Category.{u} C]
    {F G : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (η : F ⟶ G) :
    SSet.Truncated.Edge
      (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve G)) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorEdgeFromPrism (qCatDiagramNaturalTransformationPrism η)
    (qCatDiagramNaturalTransformationPrism_zero η)
    (qCatDiagramNaturalTransformationPrism_one η)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
