module

public import SerrePositivity.InfinityCategories.F1.KanEnrichedDiagramOppositeComparison
public import SerrePositivity.InfinityCategories.F1.StrictTransportDomains
public import SerrePositivity.InfinityCategories.F1.LeftCoherentTransportReconstruction
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningVertices

/-!
概要：strict transport の直値と反転係数を全 left fibrations の共同族で比較する。
方針：under の切断の豊穣図式に、Hom と係数の共通解像の大域的な比較を適用する。
規約：始域は left fibrations の Hom を解像した豊穣圏。全高次の作用を保持する。
使われ方：対象ごとの相対表現の比較を共同族へ拡張する主経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 全 left fibrations の strict transport の反転係数を、解像した Hom 上で共同実現する。 -/
def leftStraighteningOppositeCoherentMap (C : Type u) [Category.{u} C] :
    SimplicialNerve (EdgewiseEnrichedObject (LeftFibrationObject (nerve C))) ⟶
      SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) :=
  (relativeSectionEnrichedDiagram (strictTransportDomains C)).opposite.realization

/-- 直値と反転係数の strict transport は、全対象・全高次で一つの関手同型を持つ。 -/
def leftStraighteningCoherentMap_oppositeIso (C : Type u) [Category.{u} C] :
    FunctorIso
      (edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve C)) ≫
        leftStraighteningCoherentMap C)
      (leftStraighteningOppositeCoherentMap C) := by
  have e := (relativeSectionEnrichedDiagram (strictTransportDomains C)).oppositeRealizationIso
  rw [strictTransportDomains_realization] at e
  exact e

/-- 反転係数の共同実現は、各 fibration で既存の coherent transport の図式全体を回収する。 -/
lemma leftStraighteningOppositeCoherentMap_vertex {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p] :
    (leftStraighteningOppositeCoherentMap C).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex (show EdgewiseEnrichedObject (LeftFibrationObject (nerve C)) from
        ⟨leftFibrationObjectOf p, trivial⟩)) =
      functorVertex (leftCoherentTransport p) := by
  rw [leftStraighteningOppositeCoherentMap, KanEnrichedDiagram.realization_vertex,
    KanEnrichedDiagram.opposite_evaluate]
  rfl

/-- 対象ごとの直値と反転係数の比較を、同じ全対象の関手同型の成分として取り出す。 -/
def leftStraighteningCoherentMap_oppositeVertexIso {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p] :
    FunctorIso (leftStraighteningCandidate p) (leftCoherentTransport p) := by
  let X : EdgewiseEnrichedObject (LeftFibrationObject (nerve C)) :=
    ⟨leftFibrationObjectOf p, trivial⟩
  have h : (edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve C)) ≫
      leftStraighteningCoherentMap C).app (Opposite.op ⦋0⦌) (coherentNerveVertex X) =
        functorVertex (leftStraighteningCandidate p) :=
    (congrArg ((leftStraighteningCoherentMap C).app (Opposite.op ⦋0⦌))
      (coherentNerveMap_vertex (edgewiseEnrichedRight (LeftFibrationObject (nerve C))) X)).trans
        (leftStraighteningCoherentMap_vertex p)
  exact (eqToIso (congrArg HomotopyCategory.mk h)).symm ≪≫
    (leftStraighteningCoherentMap_oppositeIso C).app (coherentNerveVertex X) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (leftStraighteningOppositeCoherentMap_vertex p))

end SerrePositivity.InfinityCategories
