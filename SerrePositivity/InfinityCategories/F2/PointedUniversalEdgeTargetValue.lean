module

public import SerrePositivity.InfinityCategories.F2.PointedUniversalEdgeValuePrecomp

/-!
概要：元の指定一点普遍比較の実終点の値を、同じ canonical 区間の実終点の値へ戻す。
方針：元の両端と実辺の表示等式を消去する。
規約：HEq から端点の等式を取り出さない。使われ方：長辺二因子の同じ中間頂点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 同じ実辺・両端表示で、指定一点普遍比較の実終点の値も厳密に整合する。 -/
lemma pointedIntervalUniversalIso_target_value_change
    {K L : KanObject.{u}} (f : K ⟶ L) {C : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y)
    (hx : x = spaceInfinityVertex K) (hy : y = spaceInfinityVertex L)
    (he : e.edge = (pointedRightMorphismEdge f).edge)
    (q : C ⟶ vertexFiber pointedSpaceProjection x) :
    (q ≫ (functorVertexEquiv _ _).symm
      ((parametrizedFiberTransport pointedSpaceProjection x y).app (Opposite.op ⦋0⦌)
        ((SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e)).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1))))) ≫ pointedFiberValueTo hy =
    (q ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) hx)) ≫
      (functorVertexEquiv _ _).symm
        ((parametrizedFiberTransport pointedSpaceProjection (spaceInfinityVertex K)
          (spaceInfinityVertex L)).app (Opposite.op ⦋0⦌)
            (intervalMappingVertexOfEdge (pointedRightMorphismEdge f))) ≫
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom := by
  cases hx
  cases hy
  have hh : e = pointedRightMorphismEdge f := SSet.Edge.ext he
  subst e
  simp only [pointedFiberValueTo, eqToHom_refl, Category.comp_id]
  rw [SSet.yonedaEquiv_symm_zero]
  rfl

end SerrePositivity.InfinityCategories.F2
