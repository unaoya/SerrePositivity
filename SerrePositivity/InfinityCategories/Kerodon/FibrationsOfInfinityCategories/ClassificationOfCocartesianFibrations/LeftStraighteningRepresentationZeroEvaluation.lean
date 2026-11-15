module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentationRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexFirstVertexZero

/-! 元の指定表現同型の前合成・評価を、同じ構成の法則で照合する。 -/

@[expose] public section
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
lemma leftStraighteningInfinityDiagram_representationIso_zero_evaluate_arrow {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) (b : B _⦋0⦌) :
    let k := transportSimplexFirstVertexMap B
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso p R).hom
      (ULift.up b)) =
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagram_firstVertexTransportIso p ≪≫
      nerveCoherentTransportRepresentationIso (pullback.snd p k) (R.nativeRestrict k)).hom
        (ULift.up (nerveVertex (transportSimplexIndex b)))) := by
  dsimp only
  let x : ((SSet.uliftFunctor.{u+1,u}).obj (nerve (TransportSimplexCategory B))) _⦋0⦌ :=
    ULift.up (nerveVertex (transportSimplexIndex b))
  have h := congrArg Arrow.mk (leftStraighteningInfinityDiagram_representationIso_precomp_evaluate p R x)
  have hx := congrArg (fun v : ((SSet.uliftFunctor.{u+1,u}).obj B) _⦋0⦌ =>
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso p R).hom v))
    (transportSimplexFirstVertexMap_ulift_zero_vertex b)
  exact hx.symm.trans h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

end
