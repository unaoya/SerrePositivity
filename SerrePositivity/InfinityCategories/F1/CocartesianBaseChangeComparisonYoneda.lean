module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeJointComparisonEdge

/-!
概要：元の比較辺の一単体は、同じ転置した区間族の Yoneda 表現。
方針：標準区間の恒等単体と既存の元の比較辺を厳密に同定する。
規約：比較の代表や全パラメーターを変更しない。
使われ方：元の比較三角形の面を既存の同じ比較辺へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の比較辺は、同じ元の転置区間族の Yoneda 表現そのもの。 -/
lemma cocartesianBaseChangeJointComparisonEdge_yoneda
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) :
    SSet.yonedaEquiv (transposeFunctorFamily (cocartesianBaseChangeJointIntervalFamily k)) =
      (cocartesianBaseChangeJointComparisonEdge k).edge := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) = homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  change SSet.yonedaEquiv
    (transposeFunctorFamily (cocartesianBaseChangeJointIntervalFamily k)) =
      (transposeFunctorFamily (cocartesianBaseChangeJointIntervalFamily k)).app
        (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge
  simpa only [Category.id_comp, hi] using SSet.yonedaEquiv_comp
    (𝟙 (Δ[1] : SSet.{u + 1}))
    (transposeFunctorFamily (cocartesianBaseChangeJointIntervalFamily k))

end SerrePositivity.InfinityCategories
