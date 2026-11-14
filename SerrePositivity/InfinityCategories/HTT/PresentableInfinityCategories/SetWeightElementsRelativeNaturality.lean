module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightPointedIntervalBase
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningRestrictedWitness

/-!
概要：元の elementsComparisonNatural は、重みの射に沿って相対写像空間内で自然である。
方針：元の pointed 区間族と、元の写像空間の普遍族の制限を相対延長の可縮性で比較する。
規約：底は元の nerve の宇宙持ち上げで固定し、必要な比較同型を仮定しない。
使われ方：G8 の篩包含の四角形①で、relativePreIso に渡す実際の頂点同型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I]

/-- 元の小さい要素の圏の比較を、同じ全空間の縮小同型で大きい表示へ移す。 -/
def setWeightElementsUnstraightening (X : I ⥤ Type u) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve X.Elements) ⟶ leftUnstraightening (spaceDiagram X) :=
  (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.elementsComparisonNatural X) ≫
    (smallLeftUnstraighteningIso (spaceDiagram X)).hom

/-- 大きい表示へ移しても、元の要素の圏の射影を保つ。 -/
lemma setWeightElementsUnstraightening_projection (X : I ⥤ Type u) :
    setWeightElementsUnstraightening X ≫ leftUnstraighteningProjection (spaceDiagram X) =
      (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X) := by
  rw [setWeightElementsUnstraightening, Category.assoc, smallLeftUnstraighteningIso_projection,
    ← Functor.map_comp, SetWeight.elementsComparisonNatural_projection]

/-- 終域の元の比較を mapElements で制限しても、始域の元の射影を保つ。 -/
lemma setWeightElementsUnstraightening_map_projection {X Y : I ⥤ Type u} (φ : X ⟶ Y) :
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements) ≫
      setWeightElementsUnstraightening Y) ≫ leftUnstraighteningProjection (spaceDiagram Y) =
        (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X) := by
  rw [Category.assoc, setWeightElementsUnstraightening_projection, ← Functor.map_comp]
  rfl

/-- 元の比較と元の重みの辺の作用の二経路は、底を固定した相対写像空間内で同型である。 -/
def setWeightElementsUnstraightening_naturality {X Y : I ⥤ Type u} (φ : X ⟶ Y) :
    VertexIso
      (relativeFunctorVertex (leftUnstraighteningProjection (spaceDiagram Y))
        ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X))
        (setWeightElementsUnstraightening X ≫
          leftUnstraighteningEdgeLiftMap (spaceDiagram X) (spaceDiagram Y) (SetWeight.spaceDiagramEdge φ))
        (by rw [Category.assoc, leftUnstraighteningEdgeLiftMap_projection,
          setWeightElementsUnstraightening_projection]))
      (relativeFunctorVertex (leftUnstraighteningProjection (spaceDiagram Y))
        ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X))
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements) ≫
          setWeightElementsUnstraightening Y)
        (setWeightElementsUnstraightening_map_projection φ)) := by
  apply leftUnstraighteningRestrictedWitnessIso
    (spaceDiagram X) (spaceDiagram Y) (SetWeight.spaceDiagramEdge φ)
    ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X))
    (setWeightElementsUnstraightening X) (setWeightElementsUnstraightening_projection X)
    (setWeightPointedInterval φ)
  · change simplexPrismVertex 1 0 _ ≫ _ = _
    simpa only [setWeightElementsUnstraightening, Category.assoc, setWeightElementsPointed] using
      setWeightPointedInterval_zero φ
  · exact setWeightPointedInterval_projection φ
  · change simplexPrismVertex 1 1 _ ≫ _ = _
    simpa only [setWeightElementsUnstraightening, Category.assoc, setWeightElementsPointed] using
      setWeightPointedInterval_one φ

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
