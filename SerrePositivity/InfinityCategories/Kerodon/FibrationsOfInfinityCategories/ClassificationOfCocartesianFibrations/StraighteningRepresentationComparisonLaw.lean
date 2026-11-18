module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveRepresentationComparisonLaw
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationComparisonRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StraighteningBaseChangeRestriction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence

/-!
概要：元の全分類比較は、同じ表現空間内の指定比較との合成を保つ。
方針：同じ初頂点上の比較で合成則を示し、既存の充満忠実な制限で反映する。
規約：Kerodon §5.6（Tag 027M）、HTT §3.3.2の既存構成の比較・制限の法則。
使われ方：S8 の指定した分類・復元と余単位の比較における選択の照合。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance comparisonLaw_pullback_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 同じ指定分類比較に表現空間内の比較を続けると、元の直接比較に一致する。 -/
lemma leftStraighteningInfinityDiagram_representationIso_comp_diagramIso
    {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (R S : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    (a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
    leftStraighteningInfinityDiagram_representationIso p R ≪≫ R.diagramIso S a =
      leftStraighteningInfinityDiagram_representationIso p S := by
  let k₀ := transportSimplexFirstVertexMap B
  let k := (SSet.uliftFunctor.{u + 1, u}).map k₀
  let ff := localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B) SpaceInfinity.{u}
  have hpre (T : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
      (leftStraighteningInfinityDiagram_representationIso p T).precomp k =
        leftStraighteningInfinityDiagram_firstVertexTransportIso p ≪≫
          nerveCoherentTransportRepresentationIso (pullback.snd p k₀) (T.nativeRestrict k₀) := by
    apply Iso.ext
    rw [functorIso_precomp_hom]
    exact ff.toHoFullyFaithful.map_preimage _
  have he := R.cartesianRestrict_diagramIso S a
    ((SSet.uliftFunctor.{u + 1, u}).map (pullback.fst p k₀)) k (ulift_isPullback p k₀)
  apply functorIso_precomp_injective k ff
  rw [functorIso_precomp_trans, hpre R, hpre S, ← he, Iso.trans_assoc]
  exact congrArg (fun e => leftStraighteningInfinityDiagram_firstVertexTransportIso p ≪≫ e)
    (nerveCoherentTransportRepresentationIso_comp_diagramIso (pullback.snd p k₀)
      (R.nativeRestrict k₀) (S.nativeRestrict k₀)
      (R.cartesianRestrictVertexIso S a
        ((SSet.uliftFunctor.{u + 1, u}).map (pullback.fst p k₀)) k (ulift_isPullback p k₀)))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
