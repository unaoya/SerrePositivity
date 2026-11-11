module

public import SerrePositivity.EInfinity.Hammock.TwoIndexCoproduct
public import SerrePositivity.EInfinity.Hammock.StagePushoutNaturality
public import SerrePositivity.EInfinity.Hammock.WeakLengthBoundary

/-!
# proper 図式の元の次段階の弱同値

概要：成分ごとの弱同値は、元の段階の弱同値性を次段階へ伝える。
方針：境界と最大語の余積の比較を反転し、境界包含側を単射として pushout を貼る。
規約：前段階への貼り合わせ射の単射性を仮定しない。
使われ方：長さ濾過の全有限段階の帰納。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories

variable {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G)
  (hF : ProperDiagram F) (hG : ProperDiagram G)
  (hη : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app a))

include hF hG hη in
lemma weakStageBoundarySumMap (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (stageBoundarySumMap η n) :=
  weakTwoIndexCoproduct (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.maximalAlternatingEquiv n) _
    (fun a => lengthBoundaryMap η n a.val) (fun a => weakLengthBoundaryMap η hF hG hη n a.val)

include hη in
lemma weakStageTopSumMap (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (stageTopSumMap η n) :=
  weakTwoIndexCoproduct (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.maximalAlternatingEquiv n) _ (fun a => η.app a.val)
    (fun a => hη a.val)

include hF hG hη in
lemma weakLengthStageMap_succ (n : ℕ)
    (hn : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η (n + 1)) := by
  have := stageBoundarySumInclusion_mono (F := F) n
  have := stageBoundarySumInclusion_mono (F := G) n
  exact weakPushout_gluing (lengthStage_isPushout n hF).flip
    (lengthStage_isPushout n hG).flip (stageBoundarySumMap η n) (stageTopSumMap η n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η (n + 1))
    (stageBoundarySumMap_inclusion η n) (stageBoundarySumMap_attach η n hF hG)
    (stageTopSumMap_inclusion η n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap_transition η (Nat.le_succ n)).symm
    (weakStageBoundarySumMap η hF hG hη n) (weakStageTopSumMap η hη n) hn

end SerrePositivity.EInfinity.Hammock
