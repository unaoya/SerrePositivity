module
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerSquareSpanSourceFiber
public import SerrePositivity.InfinityCategories.Stable.ContractibleBaseInitialFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.VertexFiberMapFiber

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
namespace SerrePositivity.InfinityCategories

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroCornerSquareSpanSourceFiber_hasInitial {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌)
    (b : (vertexFiber (zeroOuterSpanSource X) x) _⦋0⦌) :
    ∃ v : (vertexFiber (zeroCornerSquareSpanSourceFiberMap X x) b) _⦋0⦌,
      IsInitialVertex v :=
  vertexFiber_hasInitial_of_contractible_base_of_equivalenceLifting
    (zeroCornerSquareSpanSourceFiberMap X x)
    (zeroCornerSquareSpanSourceFiberMap_kanEquivalenceLifting X x)
    (zeroOuterSpanSourceFiber_isContractibleKan X x) b
    (zeroCornerSquareSourceFiber_hasInitial s hs hΩ x)

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroCornerSquareFixedSpanFiber_hasInitial {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌)
    (b : (vertexFiber (zeroOuterSpanSource X) x) _⦋0⦌) :
    ∃ v : (vertexFiber (zeroCornerSquareSpan X) b.val) _⦋0⦌, IsInitialVertex v := by
  let e := HomotopyLimits.vertexFiberMapFiberIso
    (zeroCornerSquareSource X) (zeroOuterSpanSource X) (zeroCornerSquareSpan X)
    (zeroCornerSquareSpan_source X) x b
  obtain ⟨v, hv⟩ := zeroCornerSquareSpanSourceFiber_hasInitial s hs hΩ x b
  exact ⟨e.hom.app (Opposite.op ⦋0⦌) v, hv.map_of_isIso e.hom⟩
end SerrePositivity.InfinityCategories
