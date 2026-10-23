module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroEndpointHomAction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedOppositeHomAction

/-!
概要：元の指定比較の実終点辺は元の反転精密化を全 Hom 作用族へ送った path。
方針：同じ実円柱を uncurry で検出し、同じ fiber 包含で反映する。
規約：元の辺の全一単体を保持し、別の path の存在へ弱めない。
使われ方：実円柱の等式から既存の指定同型のホモトピー類の等式への移行。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "j" => simplexPrismVertex 2 2 A
local notation "y" => coherentNerveVertex L

/-- 元の指定比較の実終点辺を curry すると元の反転精密化の同じ全 Hom 作用 path。 -/
lemma spaceCompositionZeroEndpointEdge_yoneda_eq_opposite_action :
    SSet.yonedaEquiv.symm
      (spaceCompositionZeroEndpointEdge s j y (spaceCompositionZeroEndpoint_base s)).edge =
    SSet.yonedaEquiv.symm (ULift.up (SSet.opObjEquiv.symm (coherentTriangleHomotopy s))) ≫
      pointedOppositeHomAction K L := by
  apply uncurry_injective
  apply (cancel_mono (vertexFiberι pointedSpaceProjection y)).mp
  rw [pointedOppositeHomAction_uncurry]
  exact spaceCompositionZeroEndpointEdge_hom_action s

/-- 元の実終点辺の一単体は全反転 Hom の同じ係数の作用の像。 -/
lemma spaceCompositionZeroEndpointEdge_eq_opposite_action :
    (spaceCompositionZeroEndpointEdge s j y (spaceCompositionZeroEndpoint_base s)).edge =
      (pointedOppositeHomAction K L).app (Opposite.op ⦋1⦌)
        (ULift.up (SSet.opObjEquiv.symm (coherentTriangleHomotopy s))) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [spaceCompositionZeroEndpointEdge_yoneda_eq_opposite_action,
    SSet.yonedaEquiv_symm_comp]

end SerrePositivity.InfinityCategories.F2
