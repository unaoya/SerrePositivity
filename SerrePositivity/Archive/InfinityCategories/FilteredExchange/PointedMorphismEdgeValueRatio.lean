module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismIntervalFactor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedUniversalEdgeValueTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：元の raw 辺値比較の逆と同じ指定普遍比較の値を、同じ右作用比較へ戻す。
方針：元の両端・実辺を消去し、元の canonical 二因子の第一因子を消去する。
規約：元の指定値を保持。使われ方：元の長辺評価比較の同じ右作用因子の回収。
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

/-- 元の raw 辺値比較の逆と指定普遍比較の値の合成は、同じ元の右作用比較の前合成。 -/
lemma pointedMorphismEdgeValueRatio_heq_action {K L : KanObject.{u}} (f : K ⟶ L) {C : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y)
    (hx : x = spaceInfinityVertex K) (hy : y = spaceInfinityVertex L)
    (he : e.edge = (pointedRightMorphismEdge f).edge)
    (q : C ⟶ vertexFiber pointedSpaceProjection x) :
    HEq ((FunctorIso.precomp (pointedSpaceMorphismEdgeValueIso f e hx hy he) q).symm ≪≫
      ((pointedIntervalTransportAt_universalIso
        (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))).precomp q).postcomp (pointedFiberValueTo hy))
      ((pointedValueMorphismUniversalActionIso f).precomp
        (q ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) hx))) := by
  cases hx
  cases hy
  have hh : e = pointedRightMorphismEdge f := SSet.Edge.ext he
  subst e
  simp only [eqToHom_refl, pointedFiberValueTo]
  unfold pointedSpaceMorphismEdgeValueIso
  simp only [eqToHom_refl, functorIso_precomp_id]
  change HEq (((pointedValueMorphismIntervalIso f).precomp q).symm ≪≫
    ((pointedIntervalTransportAt_universalIso
      (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge (pointedRightMorphismEdge f)))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))).precomp q).postcomp
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom)
    ((pointedValueMorphismUniversalActionIso f).precomp q)
  rw [functorIso_precomp_postcomp, ← functorIso_precomp_symm, ← functorIso_precomp_trans,
    pointedValueMorphismIntervalIso_factor]
  simp only [Iso.trans_symm, Iso.trans_assoc,
    Iso.symm_self_id, Iso.trans_refl]
  rfl

end SerrePositivity.InfinityCategories.F2
