module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LimitColimitOpposite
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpecifiedCofiberSpan
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableOpposite
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareTranspose

/-!
概要：安定圏の始対象からの第二枝を持つ指定 cospan は極限を持つ。
方針：反転と枝の交換により終対象への第二枝を持つ span に移す。
規約：元の cospan 全体を固定し、有限極限の存在を追加で仮定しない。
使われ方：lax pullback の fiber 四角形の存在。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：第二枝の始点が始対象である指定 cospan は極限を持つ。
方針：極限を反対圏の余極限へ移し、ホーンの反転と枝の交換を使う。
規約：安定性と指定した始対象性だけを使う。
使われ方：零対象からの指定辺を保つ fiber の構成。 -/
lemma hasLimit_cospan_of_initial_second {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (r : (horn 2 2 : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((horn₂₂.ι₁₂ ≫ r).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit r := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasLimit_iff_hasColimit_op r).2
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso
    (SSet.opFunctor.map r) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso 2 2).hom).2
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso 2 2).hom ≫ SSet.opFunctor.map r) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwapIso.hom).2
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasColimit_span_of_terminal_second
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₂ ≫ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso 2 2).hom ≫ SSet.opFunctor.map r))).app (Opposite.op ⦋0⦌) _)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_right, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHornReverse_two_left, Category.assoc, ← CategoryTheory.Functor.map_comp]
  exact hz.op_isTerminalVertex

/-- 概要：第二枝の始点が零対象である指定 cospan は極限を持つ。
方針：零対象の始対象性を使う。
規約：元の第二枝を変更しない。使われ方：指定された fiber の入力。 -/
lemma hasLimit_cospan_of_zero_second {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (r : (horn 2 2 : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((horn₂₂.ι₁₂ ≫ r).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit r :=
  hasLimit_cospan_of_initial_second r hz.1

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
