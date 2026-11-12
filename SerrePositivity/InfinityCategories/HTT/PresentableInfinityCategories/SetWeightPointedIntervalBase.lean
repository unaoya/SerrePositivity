module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightIntervalCoordinates
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightPointedInterval
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramOrdinaryEdgePrism

/-!
概要：要素の圏から作った pointed 区間族が、元の重みの射の coherent な辺を被覆することを示す。
方針：元の比較の底への射影を計算し、通常の区間図式の全単体の表示に移す。
規約：底の辺は元の spaceDiagramEdge とし、別の代表辺へ取り替えない。
使われ方：G8 の四角形①の相対写像空間での比較に必要な厳密な可換条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory Limits SSet MonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I]

/-- 元の pointed 比較は、要素の圏からの元の空間値図式を被覆する。 -/
lemma setWeightElementsPointed_projection (X : I ⥤ Type u) :
    setWeightElementsPointed X ≫ pointedSpaceProjection =
      (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X) ≫ spaceDiagram X := by
  simp only [setWeightElementsPointed, Category.assoc]
  rw [pullback.condition]
  change (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.elementsComparisonNatural X) ≫
    (smallLeftUnstraighteningIso (spaceDiagram X)).hom ≫
      leftUnstraighteningProjection (spaceDiagram X) ≫ spaceDiagram X = _
  rw [← Category.assoc (smallLeftUnstraighteningIso (spaceDiagram X)).hom,
    smallLeftUnstraighteningIso_projection, ← Category.assoc,
    ← Functor.map_comp, SetWeight.elementsComparisonNatural_projection]

/-- 元の pointed 区間族は、同じ spaceDiagramEdge の全 prism の底変換である。 -/
lemma setWeightPointedInterval_projection {X Y : I ⥤ Type u} (φ : X ⟶ Y) :
    setWeightPointedInterval φ ≫ pointedSpaceProjection =
      (Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X)) ≫
        functorEdgePrism (SetWeight.spaceDiagramEdge φ) := by
  rw [setWeightPointedInterval, Category.assoc, setWeightElementsPointed_projection]
  change _ = _ ≫ functorEdgePrism (kanDiagramNaturalTransformationEdge
    (F := ⟨X ⋙ setsToKan, trivial⟩) (G := ⟨Y ⋙ setsToKan, trivial⟩)
    (SetWeight.coefficientsMap φ))
  rw [kanDiagramNaturalTransformationEdge_prism]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change enrichedFunctorOfOrderDiagram _ = enrichedFunctorOfOrderDiagram _
  congr 1
  exact congrArg (fun H ↦
    (⟨ULift.down, fun _ _ h ↦ h⟩ :
      ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙
      ((stdSimplex.objEquiv s.1).toOrderHom.toFunctor.prod' s.2.down) ⋙ H)
    (setWeightElementsInterval_coefficients φ)

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
