module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoIndexCoproduct
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.StagePushoutNaturality
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakLengthBoundary

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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.InfinityCategories

variable {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G)
  (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) (hG : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram G)
  (hη : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app a))

include hF hG hη in
lemma weakStageBoundarySumMap (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumMap η n) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakTwoIndexCoproduct (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.maximalAlternatingEquiv n) _
    (fun a => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n a.val) (fun a => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakLengthBoundaryMap η hF hG hη n a.val)

include hη in
lemma weakStageTopSumMap (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopSumMap η n) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakTwoIndexCoproduct (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.maximalAlternatingEquiv n) _ (fun a => η.app a.val)
    (fun a => hη a.val)

include hF hG hη in
lemma weakLengthStageMap_succ (n : ℕ)
    (hn : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η (n + 1)) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumInclusion_mono (F := F) n
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumInclusion_mono (F := G) n
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakPushout_gluing (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthStage_isPushout n hF).flip
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthStage_isPushout n hG).flip (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumMap η n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopSumMap η n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η (n + 1))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumMap_inclusion η n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumMap_attach η n hF hG)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopSumMap_inclusion η n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap_transition η (Nat.le_succ n)).symm
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakStageBoundarySumMap η hF hG hη n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakStageTopSumMap η hη n) hn

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
