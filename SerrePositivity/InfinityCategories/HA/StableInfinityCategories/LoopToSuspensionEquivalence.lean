module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopToSuspensionDiagrams
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSectionFromLoop

/-!
概要：元の loop 四角形の押し出し性と、全 suspension/loop 図式の比較。
方針：同じ指定点の始対象性を実固定 span へ戻し、全図式の評価を比較する。
規約：安定性は仮定しない。使われ方：HA 1.4.2.27 の一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma loopToSuspensionDiagramsOfLoopEquivalence_isQCatEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopToSuspensionDiagramsOfLoopEquivalence s hs hΩ) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramEvaluation_source_trivialKanFibration_of_loopEquivalence s hs hΩ
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)
  apply e.cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopToSuspensionDiagramsOfLoopEquivalence_evaluation]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence s hs hΩ

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
