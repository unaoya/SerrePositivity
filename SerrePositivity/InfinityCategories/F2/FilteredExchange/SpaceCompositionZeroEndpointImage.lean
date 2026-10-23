module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroSpecifiedComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeFixedExtensionEdgeEndpoint

/-!
概要：既存の零面の指定比較の終点像を元の実全係数円柱の辺として読む。
方針：同じ辺を fiber 終点評価で写し、同じ実区間の uncurry を回収する。
規約：任意の終点係数と元の指定比較の値を保持する。
使われ方：終点像と元の指定精密化の全 Hom 作用の同定。
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
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "b" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι pointedSpaceProjection (coherentNerveVertex K)

/-- 同じ実全係数円柱の辺の、任意の fiber 終点での指定像。 -/
def spaceCompositionZeroEndpointEdge {C : SSet.{u + 1}}
    (j : C ⟶ (Δ[2] : SSet.{u + 1}) ⊗ A) (y : SpaceInfinity.{u} _⦋0⦌)
    (hy : j ≫ b = SSet.const y) :=
  (spaceCompositionZeroExtensionEdge s).map
    (relativeExtensionFiberEndpoint pointedSpaceProjection b i v
      (spaceSimplexPointedFamily_boundary M) j y hy)

/-- 既存の指定比較の終点像の射は、同じ元の実円柱の終点辺の類。 -/
lemma spaceCompositionZeroComparison_endpoint_hom {C : SSet.{u + 1}}
    (j : C ⟶ (Δ[2] : SSet.{u + 1}) ⊗ A) (y : SpaceInfinity.{u} _⦋0⦌)
    (hy : j ≫ b = SSet.const y) :
    (VertexIso.map (spaceCompositionTetrahedronZeroComparison s)
      (relativeExtensionFiberEndpoint pointedSpaceProjection b i v
        (spaceSimplexPointedFamily_boundary M) j y hy)).hom =
    SSet.Truncated.HomotopyCategory.homMk (spaceCompositionZeroEndpointEdge s j y hy).toTruncated :=
  congrArg (fun h ↦ (hoFunctor.map
    (relativeExtensionFiberEndpoint pointedSpaceProjection b i v
      (spaceSimplexPointedFamily_boundary M) j y hy)).toFunctor.map h)
        (spaceCompositionTetrahedronZeroComparison_hom_eq_cylinder s)

/-- 終点像の実円柱を fiber に含めると元の全係数円柱の同じ制限。 -/
lemma spaceCompositionZeroEndpointEdge_uncurry {C : SSet.{u + 1}}
    (j : C ⟶ (Δ[2] : SSet.{u + 1}) ⊗ A) (y : SpaceInfinity.{u} _⦋0⦌)
    (hy : j ≫ b = SSet.const y) :
    uncurry (SSet.yonedaEquiv.symm (spaceCompositionZeroEndpointEdge s j y hy).edge) ≫
      vertexFiberι pointedSpaceProjection y =
        (j ▷ Δ[1]) ≫ (spaceCompositionZeroPointedHomotopy s).h :=
  relativeFixedExtensionHomotopyEdge_endpoint_uncurry pointedSpaceProjection b i v
    (spaceSimplexPointedFamily_boundary M) (spaceCompositionZeroPointedHomotopy s)
    (spaceSimplexPointedFamily_projection M) (spaceCompositionTetrahedronZeroFamily_projection s)
    (spaceSimplexPointedFamily_firstVertex M) (spaceCompositionTetrahedronZeroFamily_initial s)
    (spaceCompositionZeroPointedHomotopy_projection s)
    (spaceCompositionZeroPointedHomotopy_initial s) j y hy

end SerrePositivity.InfinityCategories.F2
