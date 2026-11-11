module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeClassifierFiberEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSourceUniversalUnit

/-!
概要：指定 loop 切断と Ω の同値性から、始点固定の全 loop 錐の始対象を得る。
方針：同じ円柱の厳密な式を照合し、証明済みの実区間族の同値性を戻す。
規約：安定性や有限余極限を先取りしない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 指定 loop 切断と Ω の同値性から、始点固定の全 loop 錐に始対象が存在する。 -/
lemma loopConeSourceFiber_hasInitial_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) x) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := by
  let e := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap_isQCatEquivalence X x).choose
  let u := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSourceUnit s hs hΩ) x
  refine ⟨e.inv.app (Opposite.op ⦋0⦌) u, ?_⟩
  exact (e.symm.isInitialVertex_iff u).mp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSourceUnit_initial s hs hΩ x)
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
