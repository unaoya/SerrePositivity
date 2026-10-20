module

public import SerrePositivity.InfinityCategories.F1.QCatDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.F1.FunctorEdgeFromPrism
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
namespace SerrePositivity.InfinityCategories

/-- 区間の単体と底の射列を、二点の順序と底の積の射列として表す。 -/
def qCatDiagramPrismBase (C : Type u) [Category.{u} C] :
    (Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 2 × C)) where
  app _ := ↾fun ⟨α, σ⟩ ↦
    ULift.up ((SimplexCategory.toCat.map α.down).toFunctor.prod' σ.down)
  naturality _ _ _ := rfl

/-- 自然変換が定める二点と底の積上の通常の図式。 -/
def qCatDiagramArrow {C : Type u} [Category.{u} C] {F G : C ⥤ QCat.{u}}
    (η : F ⟶ G) : Fin 2 × C ⥤ QCat.{u} :=
  CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ η)

/-- 同じ通常の自然変換の coherent な prism。 -/
def qCatDiagramNaturalTransformationPrism {C : Type u} [Category.{u} C]
    {F G : C ⥤ QCat.{u}} (η : F ⟶ G) :
    (Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ CatInfinity.{u} :=
  qCatDiagramPrismBase C ≫ qCatDiagramCoherentNerve (qCatDiagramArrow η)

/-- prism の零端点は元の始域図式の coherent 表示。 -/
lemma qCatDiagramNaturalTransformationPrism_zero {C : Type u} [Category.{u} C]
    {F G : C ⥤ QCat.{u}} (η : F ⟶ G) :
    prismEndpoint 0 _ ≫ qCatDiagramNaturalTransformationPrism η =
      qCatDiagramCoherentNerve F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ⟩
  change enrichedFunctorOfOrderDiagram _ = enrichedFunctorOfOrderDiagram _
  congr 1

/-- prism の一端点は元の終域図式の coherent 表示。 -/
lemma qCatDiagramNaturalTransformationPrism_one {C : Type u} [Category.{u} C]
    {F G : C ⥤ QCat.{u}} (η : F ⟶ G) :
    prismEndpoint 1 _ ≫ qCatDiagramNaturalTransformationPrism η =
      qCatDiagramCoherentNerve G := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ⟩
  change enrichedFunctorOfOrderDiagram _ = enrichedFunctorOfOrderDiagram _
  congr 1

/-- 通常の自然変換の coherent な辺は同じ二つの図式を結ぶ。 -/
def qCatDiagramNaturalTransformationEdge {C : Type u} [Category.{u} C]
    {F G : C ⥤ QCat.{u}} (η : F ⟶ G) :
    SSet.Truncated.Edge
      (X := (truncation 2).obj (CatInfinityFunctor
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))))
      (functorVertex (qCatDiagramCoherentNerve F))
      (functorVertex (qCatDiagramCoherentNerve G)) :=
  functorEdgeFromPrism (qCatDiagramNaturalTransformationPrism η)
    (qCatDiagramNaturalTransformationPrism_zero η)
    (qCatDiagramNaturalTransformationPrism_one η)

end SerrePositivity.InfinityCategories
