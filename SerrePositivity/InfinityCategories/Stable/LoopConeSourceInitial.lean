module
public import SerrePositivity.InfinityCategories.Stable.LoopConeClassifierFiberEquivalence
public import SerrePositivity.InfinityCategories.Stable.LoopSourceUniversalUnit

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
namespace SerrePositivity.InfinityCategories

/-- 指定 loop 切断と Ω の同値性から、始点固定の全 loop 錐に始対象が存在する。 -/
lemma loopConeSourceFiber_hasInitial_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    ∃ v : (vertexFiber (loopConeObjectSource X) x) _⦋0⦌, IsInitialVertex v := by
  let e := (loopConeClassifierSourceFiberMap_isQCatEquivalence X x).choose
  let u := unitCommaSectionVertex (loopSourceUnit s hs hΩ) x
  refine ⟨e.inv.app (Opposite.op ⦋0⦌) u, ?_⟩
  exact (e.symm.isInitialVertex_iff u).mp (loopSourceUnit_initial s hs hΩ x)
end SerrePositivity.InfinityCategories
