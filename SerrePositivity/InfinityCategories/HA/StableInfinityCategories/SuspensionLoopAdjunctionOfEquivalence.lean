module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionLoopInverseOfEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalenceAdjunction
/-!
概要：実 suspension と元の loop 関手の自己同値および三角式付き随伴。
方針：全関手として構成した両逆性を同値の随伴化へ送る。
規約：安定性は仮定しない。使われ方：一般安定性判定の Σ・Ω 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の実 Σ と Ω を同じ全関手として保持する。 -/
def suspensionLoopEquivalenceOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X X where
  hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctorOfLoopEquivalence s hs hΩ
  inv := s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0
  homInvIso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopInverseIsoOfLoopEquivalence s hs hΩ
  invHomIso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSuspensionInverseIsoOfLoopEquivalence s hs hΩ

/-- 元の実 Σ と Ω を同じ全関手として保持する。 -/
def suspensionLoopAdjunctionOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctorOfLoopEquivalence s hs hΩ)
      (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) :=
  (suspensionLoopEquivalenceOfLoopEquivalence s hs hΩ).toAdjunction
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.2.8" (partial := stronger-hyp) "仮定：点付き準圏で指定のループ関手が準圏同値（Lean が強い：HA は両関手が定義されればよい）。結論：懸垂を左随伴、ループを右随伴とする QCatAdjunction（一致）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopAdjunctionOfLoopEquivalence
