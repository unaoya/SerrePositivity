module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedClassification
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningEssentialSurjectivity

/-!
概要：実際の twisted arrow の共同 Hom 分類図式を、元の集合値 Hom 図式の全実現と比較する。
方針：既存の自然な elements 比較を分類関手で送り、既存の unstraightening の余単位を合成する。
規約：両変数・全高次を持つ一つの関手同型で、各対象の同型の選択にはしない。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、Corollary 5.6.0.6（Tag 028T）、
HTT 5.1.5.6 の固定した通常の Yoneda の全族比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable (C : Type u) [SmallCategory C]

/-- 元の Hom の元の圏の全分類図式は、同じ集合値 Hom 図式の全高次の実現と関手同型。
Kerodon Corollary 5.6.0.6（Tag 028T）、既存の自然な elements 比較の係数移送則。 -/
def ordinaryHomElementsRealizationIso :
    FunctorIso (leftStraighteningInfinityDiagram (nerveMap (ordinaryHomElementsProjection C)))
      (spaceDiagram (ordinaryHomBifunctor C)) :=
  leftStraighteningInfinityDiagram_mapVertexIso _ _
      (leftFibrationInfinityVertexIsoOfPrecompositionEquivalence
        (nerveMap (ordinaryHomElementsProjection C))
        (smallLeftUnstraighteningProjection (spaceDiagram (ordinaryHomBifunctor C)))
        (SetWeight.elementsComparisonNatural (ordinaryHomBifunctor C))
        (SetWeight.elementsComparisonNatural_projection (ordinaryHomBifunctor C))
        (SetWeight.elementsComparisonNatural_isPrecompositionEquivalence (ordinaryHomBifunctor C))) ≪≫
    leftStraighteningInfinityCounit (spaceDiagram (ordinaryHomBifunctor C))

/-- 実際の共同 Hom 図式と元の通常の Hom 図式の全実現は、底の指定同型を介して関手同型。
Kerodon Proposition 8.1.1.10（Tag 03JN）、Corollary 5.6.0.6（Tag 028T）、HTT 5.1.5.6。
同型は全 Hom の図式を一度に比較する。 -/
def ordinaryHomJointRealizationIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (ordinaryHomBaseIso C).hom ≫
        twistedArrowHomInfinity (nerve C))
      (spaceDiagram (ordinaryHomBifunctor C)) :=
  ordinaryHomTwistedClassificationIso C ≪≫ ordinaryHomElementsRealizationIso C

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
