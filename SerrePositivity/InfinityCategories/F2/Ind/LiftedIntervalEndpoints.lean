module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramConePointRestriction

/-!
概要：持ち上げた区間を標準区間に戻すとき、元の両端点を厳密に保つ。
方針：標準単体の宇宙同型の逆を両定値点で計算する。
規約：元の小さい区間の同じ二頂点。使われ方：元の全図式への錐の組み替え。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 大きい標準区間から元の小さい区間の持ち上げへの実際の同型の逆射。 -/
def liftedIntervalToSmall : (Δ[1] : SSet.{u + 1}) ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) :=
  (HomotopyLimits.uliftStdSimplexIso.{u, u + 1} 1).inv

/-- 標準区間の始点は、元の区間の同じ始点へ送られる。 -/
lemma liftedIntervalToSmall_first : stdSimplex.δ 1 ≫ liftedIntervalToSmall.{u} =
    diagramShapePoint (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) := by
  rw [stdSimplex.δ_one_eq_const, SSet.const_comp, diagramShapePoint,
    SSet.yonedaEquiv_symm_zero]
  rfl

/-- 標準区間の終点も、元の区間の同じ終点へ送られる。 -/
lemma liftedIntervalToSmall_last : stdSimplex.δ 0 ≫ liftedIntervalToSmall.{u} =
    diagramShapePoint (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) := by
  rw [stdSimplex.δ_zero_eq_const, SSet.const_comp, diagramShapePoint,
    SSet.yonedaEquiv_symm_zero]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
