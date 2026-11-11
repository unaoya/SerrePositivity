module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TetrahedronEdgeFaces

/-!
概要：元の三単体の二面の共有辺を、yoneda 表示の実図式の厳密な等式として保持する。
方針：元の二つの面の一次単体の等式を、同じ yoneda 同値で戻す。
規約：元の全単体を保持。使われ方：単位三角柱の二つの内部三角形の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二面で共有する一次単体の一致は、元の実図式の同じ辺の一致そのもの。 -/
lemma tetrahedronFaceDiagram_edge {X : SSet.{u}} (s : X _⦋3⦌)
    (i i' : Fin 3) (j j' : Fin 4) (h : X.δ i (X.δ j s) = X.δ i' (X.δ j' s)) :
    stdSimplex.δ i ≫ SSet.yonedaEquiv.symm (X.δ j s) =
      stdSimplex.δ i' ≫ SSet.yonedaEquiv.symm (X.δ j' s) := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

end SerrePositivity.InfinityCategories.F2
