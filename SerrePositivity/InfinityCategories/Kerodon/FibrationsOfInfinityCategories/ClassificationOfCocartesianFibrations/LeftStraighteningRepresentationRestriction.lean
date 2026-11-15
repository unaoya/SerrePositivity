module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoPrecomposition

/-! 元の指定表現同型の前合成・評価を、同じ構成の法則で照合する。 -/

@[expose] public section
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ指定構成の前合成・評価の法則。 -/
lemma leftStraighteningInfinityDiagram_representationIso_precomp {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    let k := transportSimplexFirstVertexMap B
    (leftStraighteningInfinityDiagram_representationIso p R).precomp
      ((SSet.uliftFunctor.{u+1,u}).map k) =
      leftStraighteningInfinityDiagram_firstVertexTransportIso p ≪≫
        nerveCoherentTransportRepresentationIso (pullback.snd p k) (R.nativeRestrict k) := by
  dsimp only
  unfold leftStraighteningInfinityDiagram_representationIso
  exact fullyFaithfulPreimageFunctorIso_precomp
    ((SSet.uliftFunctor.{u+1,u}).map (transportSimplexFirstVertexMap B))
    (localization_pre_isFullyFaithful
      (transportSimplexFirstVertexMap_ulift_isLocalization.{u,u+1} B) SpaceInfinity.{u}) _

/-- 同じ指定構成の前合成・評価の法則。 -/
lemma leftStraighteningInfinityDiagram_representationIso_precomp_evaluate {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p))
    (x : ((SSet.uliftFunctor.{u+1,u}).obj (nerve (TransportSimplexCategory B))) _⦋0⦌) :
    let k := transportSimplexFirstVertexMap B
    functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso p R).hom
      (((SSet.uliftFunctor.{u+1,u}).map k).app (Opposite.op ⦋0⦌) x) =
    functorHomEvaluate (leftStraighteningInfinityDiagram_firstVertexTransportIso p ≪≫
      nerveCoherentTransportRepresentationIso (pullback.snd p k) (R.nativeRestrict k)).hom x := by
  dsimp only
  unfold leftStraighteningInfinityDiagram_representationIso
  exact fullyFaithfulPreimageFunctorIso_evaluate
    ((SSet.uliftFunctor.{u+1,u}).map (transportSimplexFirstVertexMap B))
    (localization_pre_isFullyFaithful
      (transportSimplexFirstVertexMap_ulift_isLocalization.{u,u+1} B) SpaceInfinity.{u}) _ x

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

end
