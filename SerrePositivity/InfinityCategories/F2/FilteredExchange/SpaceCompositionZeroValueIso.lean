module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroEndpointNormalized

/-!
概要：元の零面の指定終点比較の値を、元の二段作用と長辺作用の間で保持する。
方針：証明済みの同じ実辺の両面による正規化を使い、元の指定値との一致を保持する。
規約：元の全係数・零面・値写像を保持。使われ方：指定三角形の値の整合式。
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
local notation "b" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι pointedSpaceProjection (coherentNerveVertex K)
local notation "j" => simplexPrismVertex 2 2 A
local notation "y" => coherentNerveVertex L
local notation "R" => relativeExtensionFiberEndpoint pointedSpaceProjection b i v
  (spaceSimplexPointedFamily_boundary M) j y (spaceCompositionZeroEndpoint_base s)

/-- 元の指定比較と同じ値の正規化を、元の両端作用の間の同型として保持する。 -/
def spaceCompositionZeroValueIso {Z : SSet.{u + 1}}
    (V : vertexFiber pointedSpaceProjection y ⟶ Z) :=
  (pointedOppositeTriangleFunctorIso s).postcomp V

/-- 正規化した値は元の零面の指定終点比較の値そのものである。 -/
lemma spaceCompositionZeroValueIso_heq_endpoint {Z : SSet.{u + 1}}
    (V : vertexFiber pointedSpaceProjection y ⟶ Z) :
    HEq (spaceCompositionZeroValueIso s V)
      (VertexIso.map (VertexIso.map (spaceCompositionTetrahedronZeroComparison s) R)
        ((ihom A).map V)) :=
  (spaceCompositionZeroComparison_endpoint_value_heq_normalized s V).symm

/-- 元の零面の指定比較の値を元の指定三角形の作用の値として読む。 -/
lemma spaceCompositionZeroValueIso_eq_normalized {Z : SSet.{u + 1}}
    (V : vertexFiber pointedSpaceProjection y ⟶ Z) :
    spaceCompositionZeroValueIso s V = (pointedOppositeTriangleFunctorIso s).postcomp V := rfl

end SerrePositivity.InfinityCategories.F2
