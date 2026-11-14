module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionLoopSectionOfEquivalence

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
def suspensionLoopInverseIsoOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctorOfLoopEquivalence s hs hΩ ≫
      (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) (𝟙 X) := by
  let b := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopSectionOfLoopEquivalence s hs hΩ
  have hb : b ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0 = 𝟙 X :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopSectionOfLoopEquivalence_source s hs hΩ
  have ht : b ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctorOfLoopEquivalence s hs hΩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopSectionOfLoopEquivalence_target s hs hΩ
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramFamilyIso_of_section s hs (b ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 ≫ s) b
    (by simp only [Category.assoc, hs, Category.comp_id])
  have h := e.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)
  simpa only [← Category.assoc, ht, hb] using h

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
def loopSuspensionInverseIsoOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctorOfLoopEquivalence s hs hΩ) (𝟙 X) := by
  let b := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopSectionOfLoopEquivalence s hs hΩ
  have hb : b ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0 = 𝟙 X :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopSectionOfLoopEquivalence_source s hs hΩ
  have ht : b ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctorOfLoopEquivalence s hs hΩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopSectionOfLoopEquivalence_target s hs hΩ
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramSourceFamilyIso s hs hΩ (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0 ≫ b) s
    (by simp only [Category.assoc, hb, Category.comp_id])
  have h := e.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1)
  simpa only [Category.assoc, ht, hs] using h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
