module

public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.Coherent.Edges

/-!
概要：元の辺を表す矢印関手頂点の両端評価を、元の同じ端点へ厳密に同定する。
方針：標準端点を面の Yoneda 単体として表示し、指定辺の二面を読む。
規約：充填性は不要。元の辺と両端点を保持する。
使われ方：矢印関手圏内の全錐の両端評価と元の全錐の厳密な照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の辺の矢印関手頂点を時刻零で評価すると、元の指定始点そのもの。 -/
lemma arrowFunctorVertex_zero {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌)
      (functorVertex (SSet.yonedaEquiv.symm e.edge)) = x := by
  have hi : stdSimplex.obj₀Equiv.symm (0 : Fin 2) =
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2)) := by
    apply stdSimplex.ext
    intro j
    fin_cases j
    rfl
  rw [evaluateFunctorAt_functorVertex, hi]
  change SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) = _
  rw [e.δ_one_yonedaEquiv_symm, Equiv.apply_symm_apply]

/-- 元の辺の矢印関手頂点を時刻一で評価すると、元の指定終点そのもの。 -/
lemma arrowFunctorVertex_one {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌)
      (functorVertex (SSet.yonedaEquiv.symm e.edge)) = y := by
  have hi : stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2)) := by
    apply stdSimplex.ext
    intro j
    fin_cases j
    rfl
  rw [evaluateFunctorAt_functorVertex, hi]
  change SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) = _
  rw [e.δ_zero_yonedaEquiv_symm, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.HomotopyLimits
