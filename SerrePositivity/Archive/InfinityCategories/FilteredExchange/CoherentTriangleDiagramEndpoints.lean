module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationPointTriangle

/-!
概要：元の三角形の図式側の辺の端点を、元の二つの空間値へ厳密に同定する。
方針：指定第二面を実辺の表示へ戻し、その始点と終点の等式を使う。
規約：始域 fiber の非空性は使わない。使われ方：端点評価の fiber 表示の明示的な移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 実辺の Yoneda 表示の零頂点は、指定された元の始点。 -/
lemma edgeSimplex_source_value {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = x := by
  have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    decide
  have he := congrArg SSet.yonedaEquiv (edgeSimplex_source e)
  rw [← hv, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply] at he
  exact he

/-- 実辺の Yoneda 表示の一頂点は、指定された元の終点。 -/
lemma edgeSimplex_target_value {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = y := by
  have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    decide
  have he := congrArg SSet.yonedaEquiv (edgeSimplex_target e)
  rw [← hv, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply] at he
  exact he

variable {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌}
  {y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌}
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "D" => coherentTransformationPointDiagram T.diagram b

/-- 図式側の辺の始点は元の中間の空間値。 -/
lemma coherentTriangleDiagram_source_vertex :
    (stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = G.app (Opposite.op ⦋0⦌) b := by
  rw [coherentTransformationPointDiagram_second, coherentTransformationPointDiagram_edge]
  exact edgeSimplex_source_value (functorEdgeAt (intervalMappingEdgeOfVertex y) b)

/-- 図式側の辺の終点は元の最後の空間値。 -/
lemma coherentTriangleDiagram_target_vertex :
    (stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = J.app (Opposite.op ⦋0⦌) b := by
  rw [coherentTransformationPointDiagram_second, coherentTransformationPointDiagram_edge]
  exact edgeSimplex_target_value (functorEdgeAt (intervalMappingEdgeOfVertex y) b)

end SerrePositivity.InfinityCategories.F2
