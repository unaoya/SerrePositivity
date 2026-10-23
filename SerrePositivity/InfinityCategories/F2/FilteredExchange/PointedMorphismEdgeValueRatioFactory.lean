module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismEdgeValueRatio

/-!
概要：同じ raw 辺の二因子の比を、任意の実辺上で先に構成して実初期係数で制限する。
方針：元の二因子を変えずに、一般の辺で型を固定して前合成の合成則を適用する。
規約：元の指定値を保持。使われ方：元の長辺で大きな輸送データの展開を分割する。
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
variable {K L : KanObject.{u}} (f : K ⟶ L)
  {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y)
  (hx : x = spaceInfinityVertex K) (hy : y = spaceInfinityVertex L)
  (he : e.edge = (pointedRightMorphismEdge f).edge)
local notation "a" => SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)

/-- 元の raw 値比較の逆と指定一点普遍比較の値の、同じ実初期 fiber 上の合成。 -/
def pointedMorphismEdgeValueRatio :
    FunctorIso (pointedFiberValueTo hx ≫ (SSet.uliftFunctor.{u + 1, u}).map f)
      ((functorVertexEquiv _ _).symm
        ((parametrizedFiberTransport pointedSpaceProjection x y).app (Opposite.op ⦋0⦌)
          (NatTrans.app a (Opposite.op ⦋0⦌) l)) ≫ pointedFiberValueTo hy) :=
  (pointedSpaceMorphismEdgeValueIso f e hx hy he).symm ≪≫
    (pointedIntervalTransportAt_universalIso a l).postcomp (pointedFiberValueTo hy)

/-- 元の任意の全初期係数で制限しても、同じ元の二因子の指定値を厳密に回収する。 -/
lemma pointedMorphismEdgeValueRatio_precomp_eq_factors {C : SSet.{u + 1}}
    (q : C ⟶ vertexFiber pointedSpaceProjection x) :
    (pointedMorphismEdgeValueRatio f e hx hy he).precomp q =
      (FunctorIso.precomp (pointedSpaceMorphismEdgeValueIso f e hx hy he) q).symm ≪≫
        ((pointedIntervalTransportAt_universalIso a l).precomp q).postcomp
          (pointedFiberValueTo hy) := by
  unfold pointedMorphismEdgeValueRatio
  rw [functorIso_precomp_trans, functorIso_precomp_symm, functorIso_precomp_postcomp]

/-- 同じ全初期係数での比は、元の同じ右作用比較の対応する初期係数での値。 -/
lemma pointedMorphismEdgeValueRatio_precomp_heq_action {C : SSet.{u + 1}}
    (q : C ⟶ vertexFiber pointedSpaceProjection x) :
    HEq ((pointedMorphismEdgeValueRatio f e hx hy he).precomp q)
      ((pointedValueMorphismUniversalActionIso f).precomp
        (q ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) hx))) := by
  rw [pointedMorphismEdgeValueRatio_precomp_eq_factors]
  exact pointedMorphismEdgeValueRatio_heq_action f e hx hy he q

/-- 元の raw 辺値比較を先に合成すると、同じ元の指定普遍比較の値を回収する。 -/
lemma pointedMorphismEdgeValueRatio_precomp_cancel {C : SSet.{u + 1}}
    (q : C ⟶ vertexFiber pointedSpaceProjection x) :
    (pointedSpaceMorphismEdgeValueIso f e hx hy he).precomp q ≪≫
      (pointedMorphismEdgeValueRatio f e hx hy he).precomp q =
    FunctorIso.precomp
      ((pointedIntervalTransportAt_universalIso a l).postcomp (pointedFiberValueTo hy)) q := by
  rw [← functorIso_precomp_trans]
  unfold pointedMorphismEdgeValueRatio
  simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]

end SerrePositivity.InfinityCategories.F2
