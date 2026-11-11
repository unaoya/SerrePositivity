module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramOppositeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportDomains
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftCoherentTransportReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningVertices

/-!
概要：strict transport の直値と反転係数を全 left fibrations の共同族で比較する。
方針：under の切断の豊穣図式に、Hom と係数の共通解像の大域的な比較を適用する。
規約：始域は left fibrations の Hom を解像した豊穣圏。全高次の作用を保持する。
使われ方：対象ごとの相対表現の比較を共同族へ拡張する主経路。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 全 left fibrations の strict transport の反転係数を、解像した Hom 上で共同実現する。 -/
def leftStraighteningOppositeCoherentMap (C : Type u) [Category.{u} C] :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C))) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.strictTransportDomains C)).opposite.realization

/-- 直値と反転係数の strict transport は、全対象・全高次で一つの関手同型を持つ。 -/
def leftStraighteningCoherentMap_oppositeIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap C)
      (leftStraighteningOppositeCoherentMap C) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.strictTransportDomains C)).oppositeRealizationIso
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.strictTransportDomains_realization] at e
  exact e

/-- 反転係数の共同実現は、各 fibration で既存の coherent transport の図式全体を回収する。 -/
lemma leftStraighteningOppositeCoherentMap_vertex {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    (leftStraighteningOppositeCoherentMap C).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C)) from
        ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p, trivial⟩)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p) := by
  rw [leftStraighteningOppositeCoherentMap, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.realization_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.opposite_evaluate]
  rfl

/-- 対象ごとの直値と反転係数の比較を、同じ全対象の関手同型の成分として取り出す。 -/
def leftStraighteningCoherentMap_oppositeVertexIso {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p) := by
  let X : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C)) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p, trivial⟩
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p) :=
    (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap C).app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedRight (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C))) X)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap_vertex p)
  exact (eqToIso (congrArg HomotopyCategory.mk h)).symm ≪≫
    (leftStraighteningCoherentMap_oppositeIso C).app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (leftStraighteningOppositeCoherentMap_vertex p))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
