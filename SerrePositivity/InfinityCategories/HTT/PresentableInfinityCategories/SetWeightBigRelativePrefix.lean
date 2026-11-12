module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightElementsRelativeNaturality
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightUnstraighteningEdgePrecomposition

/-!
概要：元の pinched 写像空間から要素の圏上の相対関手空間への比較は、重みの射に全族で自然である。
方針：元の辺の前合成比較と、要素の圏の相対自然性に relativePreIso を適用して合成する。
規約：底を固定した元の比較を用い、指定辺の作用も保持する。
使われ方：G8 の四角形①を元の小さい切断表示へ移す前の、大きい相対表示での四角形。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I]

/-- 元の要素の圏の比較を、大きい底上の射として束縛する。 -/
def setWeightElementsComparisonOver (X : I ⥤ Type u) :
    Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X)) ⟶
      Over.mk (leftUnstraighteningProjection (spaceDiagram X)) :=
  Over.homMk (setWeightElementsUnstraightening X) (setWeightElementsUnstraightening_projection X)

/-- 元の mapElements を、同じ大きい底上の射として束縛する。 -/
def setWeightElementsBaseMap {X Y : I ⥤ Type u} (φ : X ⟶ Y) :
    Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X)) ⟶
      Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection Y)) :=
  Over.homMk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements)) (by
    change (SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection Y) =
        (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X)
    rw [← Functor.map_comp]
    rfl)

/-- 元の pinched 比較と、元の要素の圏の比較による前合成の全写像。 -/
def setWeightBigRelativePrefix (X : I ⥤ Type u)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u}) :
    Basic.pinchedHom (functorVertex (spaceDiagram X)) (functorVertex G) ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G)
        ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X)) :=
  leftUnstraighteningPinchedMappingSpaceMap (spaceDiagram X) G ≫
    relativeFunctorOverPre (leftUnstraighteningProjection G) (setWeightElementsComparisonOver X)

/-- 元の pinched 比較と要素の圏による前合成は、元の重みの辺に全族で自然である。 -/
def setWeightBigRelativePrefix_naturality {X Y : I ⥤ Type u} (φ : X ⟶ Y)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u}) :
    FunctorIso
      (precompose (functorVertex G)
        (SSet.Truncated.HomotopyCategory.homMk (SetWeight.spaceDiagramEdge φ).toTruncated) ≫
          setWeightBigRelativePrefix X G)
      (setWeightBigRelativePrefix Y G ≫
        relativeFunctorOverPre (leftUnstraighteningProjection G) (setWeightElementsBaseMap φ)) := by
  let jX := setWeightElementsComparisonOver X
  let jY := setWeightElementsComparisonOver Y
  let k := setWeightElementsBaseMap φ
  let e := SetWeight.spaceDiagramEdge φ
  let aX := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X))
  let bY := Over.mk (leftUnstraighteningProjection (spaceDiagram Y))
  let c := Over.mk (leftUnstraighteningProjection G)
  let t : Over.mk (leftUnstraighteningProjection (spaceDiagram X)) ⟶ bY :=
    Over.homMk (leftUnstraighteningEdgeLiftMap (spaceDiagram X) (spaceDiagram Y) e)
      (leftUnstraighteningEdgeLiftMap_projection (spaceDiagram X) (spaceDiagram Y) e)
  have hn : VertexIso (relativeFunctorVertex bY.hom aX.hom (jX ≫ t).left (jX ≫ t).w)
      (relativeFunctorVertex bY.hom aX.hom (k ≫ jY).left (k ≫ jY).w) :=
    setWeightElementsUnstraightening_naturality φ
  have h₀ := (unstraighteningPinchedEdgeLiftPrecompositionIso
    (spaceDiagram X) (spaceDiagram Y) G e).postcomp (relativeFunctorOverPre c.hom jX)
  have h₁ := (SetWeight.relativePreIso aX bY c (jX ≫ t) (k ≫ jY) hn).precomp
    (leftUnstraighteningPinchedMappingSpaceMap (spaceDiagram Y) G)
  have h₀' : FunctorIso
      (precompose (functorVertex G) (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        setWeightBigRelativePrefix X G)
      (leftUnstraighteningPinchedMappingSpaceMap (spaceDiagram Y) G ≫
        relativeFunctorOverPre c.hom (jX ≫ t)) := by
    dsimp only [jX, t, c, Over.mk, Over.hom, CostructuredArrow.mk] at h₀ ⊢
    simpa only [setWeightBigRelativePrefix, relativeFunctorOverPre_comp, Category.assoc] using h₀
  have h := h₀' ≪≫ h₁
  dsimp only [jY, k, c, e, Over.mk, Over.hom, CostructuredArrow.mk] at h ⊢
  simpa only [setWeightBigRelativePrefix, relativeFunctorOverPre_comp, Category.assoc] using h

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
