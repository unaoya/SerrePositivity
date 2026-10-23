module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityEdge

/-!
概要：同じ元の結合比較辺の一単体は、元の転置区間族の Yoneda 表現。
方針：標準区間の恒等単体と同じ標準辺を同定する。
規約：元の結合比較と全高次の族を保持する。
使われ方：第二比較の分解三角形の面を既存の元の結合比較へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の結合比較辺は、同じ元の転置区間族の Yoneda 表現そのもの。 -/
lemma cocartesianBaseChangeAssociativityEdge_yoneda
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) :
    SSet.yonedaEquiv (transposeFunctorFamily
      (cocartesianBaseChangeAssociativityIntervalFamily l k)) =
        (cocartesianBaseChangeAssociativityEdge l k).edge := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) = homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  change SSet.yonedaEquiv
    (transposeFunctorFamily (cocartesianBaseChangeAssociativityIntervalFamily l k)) =
      (transposeFunctorFamily (cocartesianBaseChangeAssociativityIntervalFamily l k)).app
        (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge
  simpa only [Category.id_comp, hi] using SSet.yonedaEquiv_comp
    (𝟙 (Δ[1] : SSet.{u + 1}))
    (transposeFunctorFamily (cocartesianBaseChangeAssociativityIntervalFamily l k))

end SerrePositivity.InfinityCategories
