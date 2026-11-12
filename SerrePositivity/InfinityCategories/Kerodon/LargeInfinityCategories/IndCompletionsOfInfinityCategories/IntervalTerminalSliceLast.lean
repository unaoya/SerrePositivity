module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IntervalTerminalSliceSection

/-!
概要：終点 slice の標準区間切断は、最後の頂点で同じ終点の恒等射となる。
方針：右二点を終点へ潰す全 join の射を計算し、uncurry を保つ。
規約：固定図式の表示を変えない。使われ方：実補間円柱の恒等終点条件。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 最後の二点を結ぶ join は、同じ終点へ定値となる。 -/
lemma intervalTerminalJoin_last :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ 0 : (Δ[0] : SSet.{u}) ⟶ Δ[1]) (𝟙 Δ[0]) ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 1 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 0 ≫ stdSimplex.δ 0 := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).mp
  apply SSet.yonedaEquiv.injective
  decide

/-- 標準区間切断の最後の全辺は、元の終点の恒等辺そのもの。 -/
lemma intervalTerminalSliceSection_last {X : SSet.{u}} (d : (Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (stdSimplex.δ 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.intervalTerminalSliceSection d) =
      SSet.const (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ d)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.intervalTerminalSliceSection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry,
    ← Category.assoc, intervalTerminalJoin_last, Category.assoc]
  have hc : stdSimplex.δ 0 ≫ d = SSet.const (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ d)) := by
    rw [← SSet.yonedaEquiv_symm_zero, Equiv.symm_apply_apply]
  exact (congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 0 ≫ f) hc).trans (SSet.comp_const _ _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
