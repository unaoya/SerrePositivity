module

public import SerrePositivity.InfinityCategories.F1B.KanLimitColimitOpposite
public import SerrePositivity.InfinityCategories.Stable.SpecifiedCofiberSpan
public import SerrePositivity.InfinityCategories.Stable.StableOpposite
public import SerrePositivity.InfinityCategories.Stable.SquareTranspose

/-!
概要：安定圏の始対象からの第二枝を持つ指定 cospan は極限を持つ。
方針：反転と枝の交換により終対象への第二枝を持つ span に移す。
規約：元の cospan 全体を固定し、有限極限の存在を追加で仮定しない。
使われ方：lax pullback の fiber 四角形の存在。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：第二枝の始点が始対象である指定 cospan は極限を持つ。
方針：極限を反対圏の余極限へ移し、ホーンの反転と枝の交換を使う。
規約：安定性と指定した始対象性だけを使う。
使われ方：零対象からの指定辺を保つ fiber の構成。 -/
lemma hasLimit_cospan_of_initial_second {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (r : (horn 2 2 : SSet.{u}) ⟶ X)
    (hz : IsInitialVertex ((horn₂₂.ι₁₂ ≫ r).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) : HasLimit r := by
  apply (F1B.kanHasLimit_iff_hasColimit_op r).2
  apply (F1B.kanHasColimit_iff_restrict_of_isIso
    (SSet.opFunctor.map r) (hornReverseIso 2 2).hom).2
  apply (F1B.kanHasColimit_iff_restrict_of_isIso
    ((hornReverseIso 2 2).hom ≫ SSet.opFunctor.map r) spanSwapIso.hom).2
  apply hasColimit_span_of_terminal_second
  change IsTerminalVertex ((horn₂₀.ι₀₂ ≫ (spanSwap ≫
    ((hornReverseIso 2 2).hom ≫ SSet.opFunctor.map r))).app (Opposite.op ⦋0⦌) _)
  rw [← Category.assoc, spanSwap_right, ← Category.assoc,
    stableHornReverse_two_left, Category.assoc, ← CategoryTheory.Functor.map_comp]
  exact hz.op_isTerminalVertex

/-- 概要：第二枝の始点が零対象である指定 cospan は極限を持つ。
方針：零対象の始対象性を使う。
規約：元の第二枝を変更しない。使われ方：指定された fiber の入力。 -/
lemma hasLimit_cospan_of_zero_second {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (r : (horn 2 2 : SSet.{u}) ⟶ X)
    (hz : IsZeroVertex ((horn₂₂.ι₁₂ ≫ r).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) : HasLimit r :=
  hasLimit_cospan_of_initial_second r hz.1

end SerrePositivity.InfinityCategories.F2
