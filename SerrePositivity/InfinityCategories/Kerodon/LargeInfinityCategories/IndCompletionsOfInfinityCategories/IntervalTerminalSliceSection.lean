module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ArrowInterpolationCoconeCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：区間図式を、その終点 slice の標準切断へ持ち上げる。
方針：区間の右余錐の最後の点を終点に潰し、同じ図式を後合成する。
規約：射影は元の全区間図式、始点の辺も元の辺。使われ方：円柱持ち上げの終端側面。

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

/-- 最初の点と最後の点を結ぶ join の評価は、同じ標準区間そのもの。 -/
lemma intervalTerminalJoin_first :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ 1 : (Δ[0] : SSet.{u}) ⟶ Δ[1]) (𝟙 Δ[0]) ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 1 = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).mp
  rw [Iso.inv_hom_id]
  apply SSet.yonedaEquiv.injective
  decide

variable {X : SSet.{u}} (d : (Δ[1] : SSet.{u}) ⟶ X)

/-- 最後の頂点を終点に潰した全余錐は、元の同じ区間の終点を持つ。 -/
lemma intervalTerminalSlice_fixed :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 1 ≫ d) =
      stdSimplex.δ 0 ≫ d := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationInterval_inr, stdSimplex.δ_zero_eq_const]

/-- 元の全区間図式を、その終点の実 slice へ持ち上げる標準切断。 -/
def intervalTerminalSliceSection : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (stdSimplex.δ 0 ≫ d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 1 ≫ d) (intervalTerminalSlice_fixed d)

/-- 標準切断は、元の全区間図式を厳密に被覆する。 -/
lemma intervalTerminalSliceSection_projection :
    intervalTerminalSliceSection d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (stdSimplex.δ 0 ≫ d) = d := by
  rw [intervalTerminalSliceSection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverCurry_projection,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_inl, Category.id_comp]

/-- 標準切断の始点側の全辺は、元の区間の同じ辺。 -/
lemma intervalTerminalSliceSection_first :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (stdSimplex.δ 1 ≫ intervalTerminalSliceSection d) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ d := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, intervalTerminalSliceSection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry, ← Category.assoc, intervalTerminalJoin_first]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
