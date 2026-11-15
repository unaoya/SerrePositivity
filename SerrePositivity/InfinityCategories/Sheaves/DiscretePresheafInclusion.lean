module

public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheaf
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.KanDiagramBundle

/-!
概要：離散前層の埋め込みを、全自然変換と全高次単体を含めて固定する。
方針：Kan 図式の既存の束縛、通常 nerve から coherent nerve への射、同じ実現を合成する。
使われ方：HTT 5.5.6.28、Kerodon Corollary 5.6.0.6（Tag 028T）。
規約：個々の集合の離散化だけで全前層関手を代用しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 同じ strict 離散図式の束縛を全通常関手として固定する。 -/
def kanDiscretePresheafFunctor (C : Type u) [SmallCategory C] :
    (Cᵒᵖ ⥤ Type u) ⥤ KanDiagramObject Cᵒᵖ :=
  (Functor.whiskeringRight Cᵒᵖ (Type u) KanObject.{u}).obj setsToKan ⋙ kanDiagramBundle

/-- 通常 nerve の全単体を、同じ Kan 図式の実現で送る。 -/
def kanDiscretePresheafMap (C : Type u) [SmallCategory C] :
    nerve (Cᵒᵖ ⥤ Type u) ⟶ PresheafCat C SpaceInfinity.{u} :=
  nerveMap (kanDiscretePresheafFunctor C) ≫ nerveToCoherent (KanDiagramObject Cᵒᵖ) ≫
    kanDiagramRealization Cᵒᵖ

/-- 埋め込みの頂点は元の離散前層の表示。 -/
lemma kanDiscretePresheafMap_vertex (P : Cᵒᵖ ⥤ Type u) :
    (kanDiscretePresheafMap C).app _ (nerveVertex P) = functorVertex (discretePresheaf P) := by
  change (kanDiagramRealization Cᵒᵖ).app (Opposite.op ⦋0⦌)
    ((nerveToCoherent (KanDiagramObject Cᵒᵖ)).app (Opposite.op ⦋0⦌)
      ((nerveMap (kanDiscretePresheafFunctor C)).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ P))) = _
  rw [nerveMap_app_mk₀, nerveToCoherent_vertex, kanDiagramRealization_vertex]
  rfl

/-- 埋め込みの辺は元の自然変換の同じ Kan 図式実現。 -/
lemma kanDiscretePresheafMap_edge {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    ((nerve.edgeMk φ).map (kanDiscretePresheafMap C)).edge =
      (kanDiagramNaturalTransformationEdge (F := ⟨P ⋙ setsToKan, trivial⟩)
        (G := ⟨Q ⋙ setsToKan, trivial⟩)
        (Functor.whiskerRight (Functor.whiskerRight φ setsToKan) kanObjectForget)).edge := by
  change (kanDiagramRealization Cᵒᵖ).app (Opposite.op ⦋1⦌)
    ((nerveToCoherent (KanDiagramObject Cᵒᵖ)).app (Opposite.op ⦋1⦌)
      ((nerveMap (kanDiscretePresheafFunctor C)).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ φ))) = _
  rw [nerveMap_app_mk₁]
  change (kanDiagramRealization Cᵒᵖ).app (Opposite.op ⦋1⦌)
    ((nerveToCoherent (KanDiagramObject Cᵒᵖ)).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ ((kanDiscretePresheafFunctor C).map φ))) =
    (kanDiagramRealization Cᵒᵖ).app (Opposite.op ⦋1⦌)
      (coherentNerveEdge ((kanDiscretePresheafFunctor C).map φ)).edge
  rw [coherentNerveEdge_edge]

/-- 元の型の頂点・辺の仕様付きの全埋め込み。 -/
def kanDiscretePresheafInclusion (C : Type u) [SmallCategory C] :
    {I : nerve (Cᵒᵖ ⥤ Type u) ⟶ PresheafCat C SpaceInfinity.{u} //
      (∀ P, I.app _ (nerveVertex P) = functorVertex (discretePresheaf P)) ∧
      (∀ {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q), ((nerve.edgeMk φ).map I).edge =
        (kanDiagramNaturalTransformationEdge (F := ⟨P ⋙ setsToKan, trivial⟩)
          (G := ⟨Q ⋙ setsToKan, trivial⟩)
          (Functor.whiskerRight (Functor.whiskerRight φ setsToKan) kanObjectForget)).edge)} :=
  ⟨kanDiscretePresheafMap C, kanDiscretePresheafMap_vertex, kanDiscretePresheafMap_edge⟩

end SerrePositivity.InfinityCategories.Sheaves
