module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroEndpointImage
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroCosliceEndpoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyTensorVertex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedVertexBase

/-!
概要：既存の指定比較の終点像は、元の実 coslice 辺を全独立 Hom へ作用させた円柱。
方針：同じ実全係数円柱を頂点で制限し、元の前合成の二因子を回収する。
規約：全係数・fiber・指定比較を保持する。
使われ方：元の指定精密化の全 Hom 作用と長辺値式の照合。
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
local notation "M" => coherentSimplexMaximalization s
local notation "j" => simplexPrismVertex 2 2 A
local notation "y" => coherentNerveVertex L
local notation "E" => coherentCosliceSourcePrecomposition pointKanObject K ≫
  pointedCoherentCosliceIso.hom

/-- 元の終頂点の底は同じ元の終点 fiber の頂点。 -/
lemma spaceCompositionZeroEndpoint_base :
    j ≫ (fst Δ[2] A ≫ SSet.yonedaEquiv.symm M) = SSet.const y :=
  spaceSimplexPointedVertex_base M 2

/-- 元の全係数円柱の終点制限は同じ実 coslice 辺と全係数の作用。 -/
lemma spaceCompositionZeroPointedHomotopy_endpoint_action :
    (j ▷ Δ[1]) ≫ (spaceCompositionZeroPointedHomotopy s).h =
    lift (snd A Δ[1] ≫ spaceCompositionZeroCosliceEndpoint s) (fst A Δ[1]) ≫ E := by
  exact (congrArg (fun h ↦ (j ▷ Δ[1]) ≫ h)
    (spaceCompositionZeroPointedHomotopy_h s)).trans
      (functorHomotopyTensorRight_postcomp_vertex
        (spaceCompositionTetrahedronZeroCosliceHomotopy s) A E (stdSimplex.obj₀Equiv.symm 2))

/-- 指定比較の同じ fiber 終点の実円柱は元の coslice 精密化の全係数作用。 -/
lemma spaceCompositionZeroEndpointEdge_action :
    uncurry (SSet.yonedaEquiv.symm
      (spaceCompositionZeroEndpointEdge s j y (spaceCompositionZeroEndpoint_base s)).edge) ≫
        vertexFiberι pointedSpaceProjection y =
      lift (snd A Δ[1] ≫ spaceCompositionZeroCosliceEndpoint s) (fst A Δ[1]) ≫ E :=
  (spaceCompositionZeroEndpointEdge_uncurry s j y (spaceCompositionZeroEndpoint_base s)).trans
    (spaceCompositionZeroPointedHomotopy_endpoint_action s)

end SerrePositivity.InfinityCategories.F2
