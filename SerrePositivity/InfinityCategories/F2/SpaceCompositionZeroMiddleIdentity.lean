module

public import SerrePositivity.InfinityCategories.F2.SpaceCompositionZeroMiddleEndpoint
public import SerrePositivity.InfinityCategories.F2.SpaceCompositionTetrahedronZeroComparison
public import SerrePositivity.InfinityCategories.F2.SpaceTrianglePointedMiddleIdentity

/-!
概要：元の零面の指定比較の中間像は、同じ実中間射の恒等同型。
方針：二実初辺の一致を同じ全比較の端点像に適用する。
規約：元の指定値を保持。使われ方：最後辺の自然性から零面の中間因子を消去する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "p" => pointedSpaceProjection
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "K₁" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1))
local notation "β" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι p (coherentNerveVertex K)
local notation "j" => simplexPrismVertex 2 1 A
local notation "y" => coherentNerveVertex K₁
local notation "g" => spaceCompositionZeroMiddleMap s

/-- 元の全零面比較の、元の同じ実中間射における指定端点像。 -/
def spaceCompositionZeroMiddleEndpointIso : FunctorIso g g :=
  spaceSimplexPointedFamilyEndpointIso M (spaceCompositionTetrahedronZeroFamily s)
    (spaceCompositionTetrahedronZeroFamily_projection s)
    (spaceCompositionTetrahedronZeroFamily_initial s) j y (spaceCompositionZeroMiddle_base s)
    g g (spaceCompositionZeroMiddleMap_standard s) (spaceCompositionZeroMiddleMap_zero s)

/-- 元の指定中間像は、同じ実中間射の恒等同型に厳密に一致する。 -/
lemma spaceCompositionZeroMiddleEndpointIso_eq_refl :
    spaceCompositionZeroMiddleEndpointIso s = Iso.refl _ :=
  spaceTrianglePointedFamilyMiddleEndpointIso_eq_refl_of_first_eq M
    (spaceCompositionTetrahedronZeroFamily s) (spaceCompositionTetrahedronZeroFamily_projection s)
    (spaceCompositionTetrahedronZeroFamily_initial s) y (spaceCompositionZeroMiddle_base s)
    g (spaceCompositionZeroMiddleMap_standard s) (spaceCompositionZeroMiddleMap_zero s)
    (spaceCompositionZeroFamily_first_eq_standard s).symm

end SerrePositivity.InfinityCategories.F2
