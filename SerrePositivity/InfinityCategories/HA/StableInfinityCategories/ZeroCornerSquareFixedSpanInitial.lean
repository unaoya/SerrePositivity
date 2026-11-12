module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCornerSquareSpanSourceFiber
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ContractibleBaseInitialFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.VertexFiberMapFiber

/-!
概要：零終点 span の可縮性と、固定した実 span 上の零隅四角形の始対象。
方針：二辺の相対持ち上げ、全制限写像、同じ厳密 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroCornerSquareSpanSourceFiber_hasInitial {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource X) x) _⦋0⦌) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpanSourceFiberMap X x) b) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.vertexFiber_hasInitial_of_contractible_base_of_equivalenceLifting
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpanSourceFiberMap X x)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpanSourceFiberMap_kanEquivalenceLifting X x)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSourceFiber_isContractibleKan X x) b
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSourceFiber_hasInitial s hs hΩ x)

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroCornerSquareFixedSpanFiber_hasInitial {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource X) x) _⦋0⦌) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X) b.val) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberMapFiberIso
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan_source X) x b
  obtain ⟨v, hv⟩ := zeroCornerSquareSpanSourceFiber_hasInitial s hs hΩ x b
  exact ⟨e.hom.app (Opposite.op ⦋0⦌) v, hv.map_of_isIso e.hom⟩
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
