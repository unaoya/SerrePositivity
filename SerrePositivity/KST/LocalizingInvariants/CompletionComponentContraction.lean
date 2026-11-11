module

public import SerrePositivity.KST.LocalizingInvariants.CompletionComponentSection
public import SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamilyNullHomotopy
public import SerrePositivity.KST.LocalizingInvariants.CompletionPrismEdges

/-!
概要：成分ごとの零分母始域から元の包含への一つの全図式ホモトピーを作る。
方針：離散成分への射と切断の合成を始点にし、零関手を通る二胞体を実現する。
規約：両端と全頂点の零分母を保持し、全 prism の所属は別に検証する。
使われ方：Sp-7 の同じ wide 部分複体内の成分収縮。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D : SSet.{u}} [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
  (f : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
local instance : Preadditive D.HomotopyCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho (X := D)

/-- 概要：元の各成分を、同じ成分の零分母始域へ送る関手。
方針：離散成分への射と切断の合成を始点にし、零関手を通る二胞体を実現する。
規約：両端と全頂点の零分母を保持し、全 prism の所属は別に検証する。
使われ方：Sp-7 の同じ wide 部分複体内の成分収縮。 -/
def completionComponentCollapse : (completionCofiberWide f : SSet.{u}) ⟶
    (completionCofiberWide f : SSet.{u}) :=
  completionComponentProjection f ≫ completionComponentSection f h

/-- 概要：同じ元の頂点での収縮始点を回収する。
方針：離散成分への射と切断の合成を始点にし、零関手を通る二胞体を実現する。
規約：両端と全頂点の零分母を保持し、全 prism の所属は別に検証する。
使われ方：Sp-7 の同じ wide 部分複体内の成分収縮。 -/
lemma completionComponentCollapse_zero (x : (completionCofiberWide f : SSet.{u}) _⦋0⦌) :
    (completionComponentCollapse f h).app _ x =
      completionComponentSectionVertex f h (SSet.π₀.mk x) := by
  change ((completionCofiberWide f : SSet.{u}).map
    (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op
    (completionComponentSectionVertex f h ((completionComponentProjection f).app _ x))) = _
  rw [show (completionComponentProjection f).app (Opposite.op ⦋0⦌) x =
      SSet.π₀.mk x from _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentLabelMap_zero _ id x]
  simp [SimplexCategory.const_eq_id]

/-- 概要：同じ二端点を持つ、周囲の安定 ∞ 圏内の全図式収縮。
方針：離散成分への射と切断の合成を始点にし、零関手を通る二胞体を実現する。
規約：両端と全頂点の零分母を保持し、全 prism の所属は別に検証する。
使われ方：Sp-7 の同じ wide 部分複体内の成分収縮。 -/
def completionAmbientContraction : SSet.Homotopy
    (completionComponentCollapse f h ≫ (completionCofiberWide f).ι)
    (completionCofiberWide f).ι :=
  ZeroArrowFamily.nullHomotopy _ _

/-- 概要：全図式収縮の各頂点成分は、元の本質像の実 cofiber 分母。
方針：離散成分への射と切断の合成を始点にし、零関手を通る二胞体を実現する。
規約：両端と全頂点の零分母を保持し、全 prism の所属は別に検証する。
使われ方：Sp-7 の同じ wide 部分複体内の成分収縮。 -/
lemma completionAmbientContraction_component
    (x : (completionCofiberWide f : SSet.{u}) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (completionAmbientContraction f h) x).edge ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f) := by
  rw [← stableClosure_completionEssentialImage f h.2.1]
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW (completionEssentialImage f) _).2
  have hz := ZeroArrowFamily.nullHomotopy_component
    (completionComponentCollapse f h ≫ (completionCofiberWide f).ι)
    (completionCofiberWide f).ι x
  change Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (completionAmbientContraction f h) x).toTruncated = 0 at hz
  rw [hz]
  change completionZeroTarget f ((completionComponentCollapse f h).app _ x).val x.val
  rw [completionComponentCollapse_zero]
  exact completionComponentSectionVertex_zeroTarget f h x

end SerrePositivity.KST.LocalizingInvariants
