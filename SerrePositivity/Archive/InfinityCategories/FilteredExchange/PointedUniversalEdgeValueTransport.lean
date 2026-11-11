module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedSpaceMorphismEdgeValueIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoSelfUnitExchange

/-!
概要：元の実辺の両端表示を、同じ canonical 区間の指定比較の値へ戻す。
方針：元の表示等式と前合成の合成則を使う。
規約：元の実辺・指定比較を保持。使われ方：raw 長辺の指定値比較の二因子の回収。
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

/-- 同じ実辺の両端表示の変更は、元の指定一点普遍比較の値の初期値移送とも整合する。 -/
lemma pointedIntervalUniversalIso_edge_value_change
    {K L : KanObject.{u}} (f : K ⟶ L)
    {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y)
    (hx : x = spaceInfinityVertex K) (hy : y = spaceInfinityVertex L)
    (he : e.edge = (pointedRightMorphismEdge f).edge) :
    HEq ((pointedIntervalTransportAt_universalIso
      (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))).postcomp (pointedFiberValueTo hy))
      (((pointedIntervalTransportAt_universalIso
        (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge (pointedRightMorphismEdge f)))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))).postcomp
          (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom).precomp
            (eqToHom (congrArg (vertexFiber pointedSpaceProjection) hx))) := by
  cases hx
  cases hy
  have hh : e = pointedRightMorphismEdge f := SSet.Edge.ext he
  subst e
  rw [eqToHom_refl, functorIso_precomp_id]
  rfl

end SerrePositivity.InfinityCategories.F2
