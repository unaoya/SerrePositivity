module
public import SerrePositivity.KST.Fibration.ZeroStableHomExtension
public import SerrePositivity.KST.Fibration.StableBoundaryKanComparison

/-! # 元の零値完全関手族の全図式比較と、同じ正反復 S• の全 Hom への移送 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 二つの元の零値完全関手族は、全パラメータを保つ関手同型で比較される。 -/
def zeroStableHomFamilyIso {T : SSet.{u}} {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (H G : T ⟶ (A ⟶[SSet.{u}] B))
    (hH : ∀ v, StableHomZeroVertex A B (H.app (Opposite.op ⦋0⦌) v))
    (hG : ∀ v, StableHomZeroVertex A B (G.app (Opposite.op ⦋0⦌) v)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso H G := by
  let Z := zeroStableHomSpace A B
  have hc := zeroStableHomSpace_isContractibleKan A B
  let : KanComplex Z := hc.kanComplex
  let : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex Z :=
    ⟨⟨hc.nonempty.some, hc.isInitialVertex _, hc.isTerminalVertex _⟩⟩
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (StableHomZeroVertex A B) H hH
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (StableHomZeroVertex A B) G hG
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (A ⟶[SSet.{u}] B) (StableHomZeroVertex A B)).ι
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F L := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso F L
    (fun v => ⟨hc.isInitialVertex _, hc.isTerminalVertex _⟩)
    (fun v => ⟨hc.isInitialVertex _, hc.isTerminalVertex _⟩)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e j

/-- 元の正反復 S• の全 Hom へ後合成しても、同じ零値関手族の全図式比較を保つ。 -/
def zeroStableHomMultiFamilyIso (r : ℕ) {T : SSet.{u}} {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (H G : T ⟶ (A ⟶[SSet.{u}] B))
    (hH : ∀ v, StableHomZeroVertex A B (H.app (Opposite.op ⦋0⦌) v))
    (hG : ∀ v, StableHomZeroVertex A B (G.app (Opposite.op ⦋0⦌) v)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (H ≫ (stableMultiKanEnrichedFunctor r).map A B)
      (G ≫ (stableMultiKanEnrichedFunctor r).map A B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (zeroStableHomFamilyIso H G hH hG)
    ((stableMultiKanEnrichedFunctor r).map A B)

end SerrePositivity.KST.Fibration
