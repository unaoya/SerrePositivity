module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentationBaseChangeFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StraighteningBaseChangeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LocalizationUlift

/-!
概要：元の指定表現比較は、底変換の元の比較と全体で両立する。
方針：初頂点制限での既存の照合を、局所化による制限の充満忠実性で反映する。
規約：HTT §3.3.2・Kerodon Tag 028Tの構成の、この指定比較での特殊な法則。
使われ方：P3-E、重み付き切断の添字と指定余単位を保つ底変換。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の指定表現比較と底変換比較は、同じ元の全族の同型として両立する。
HTT §3.3.2・Kerodon Tag 028Tの構成の、この指定局所化模型での特殊な照合。 -/
@[cite HTT "3.3.2" (partial := special) "指定表現比較と底変換の全同型としての一致。"]
lemma leftStraighteningInfinityDiagram_representationIso_baseChange :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  ∀ R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p),
  leftStraighteningInfinityDiagram_baseChangeIso p k ≪≫
    leftStraighteningInfinityDiagram_representationIso (pullback.snd p k) (R.nativeRestrict k) =
  (leftStraighteningInfinityDiagram_representationIso p R).precomp
    ((SSet.uliftFunctor.{u+1,u}).map k) := by
  intro E B D hB hD p hp k R
  let U := SSet.uliftFunctor.{u+1,u}
  let q := pullback.snd p k
  let lD := transportSimplexFirstVertexMap D
  let ff := localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u,u+1} D) SpaceInfinity.{u}
  apply functorIso_precomp_injective (U.map lD) ff
  rw [functorIso_precomp_trans,
    leftStraighteningInfinityDiagram_representationIso_precomp q (R.nativeRestrict k)]
  exact leftStraighteningRepresentation_baseChange_firstVertex p k R

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
