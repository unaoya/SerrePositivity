module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeExtensionFiberEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointTransport

/-!
概要：元の全 pointed 比較を、実際の指定 fiber 内の元の終点射の同型へ写す。
方針：同じ全比較を相対終点評価で写し、元の実両端の頂点公式だけで表示を揃える。
規約：指定比較を選び直さない。使われ方：三頂点の元の値と普遍輸送の同時比較。
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
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "b" => fst Δ[n] A ≫ SSet.yonedaEquiv.symm s
local notation "i" => scaffoldFirstVertex n ▷ A
local notation "v" => snd Δ[0] A ≫
  pointedCoherentFiberComparison (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))) ≫
    vertexFiberι pointedSpaceProjection
      (coherentNerveVertex (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))))

/-- 同じ全比較の指定終点像を、元の実際の二射の関手同型として読む。 -/
def spaceSimplexPointedFamilyEndpointIso
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v)
    {Q : SSet.{u + 1}} (r : Q ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
    (y : SpaceInfinity.{u} _⦋0⦌) (hy : r ≫ b = SSet.const y)
    (g g' : Q ⟶ vertexFiber pointedSpaceProjection y)
    (hg : r ≫ spaceSimplexPointedFamily s = g ≫ vertexFiberι pointedSpaceProjection y)
    (hg' : r ≫ L = g' ≫ vertexFiberι pointedSpaceProjection y) : FunctorIso g g' :=
  vertexIsoOfEq
    (VertexIso.map (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
      (relativeExtensionFiberEndpoint pointedSpaceProjection b i v
        (spaceSimplexPointedFamily_boundary s) r y hy))
    (relativeExtensionFiberEndpoint_vertex pointedSpaceProjection b i v
      (spaceSimplexPointedFamily_boundary s) r y hy (spaceSimplexPointedFamily s)
      (spaceSimplexPointedFamily_projection s) (spaceSimplexPointedFamily_firstVertex s) g hg)
    (relativeExtensionFiberEndpoint_vertex pointedSpaceProjection b i v
      (spaceSimplexPointedFamily_boundary s) r y hy L hL hL₀ g' hg')

/-- 実両端を揃えた終点同型も、同じ全比較の指定終点像の値を厳密に保持する。 -/
lemma spaceSimplexPointedFamilyEndpointIso_heq_map
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v)
    {Q : SSet.{u + 1}} (r : Q ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
    (y : SpaceInfinity.{u} _⦋0⦌) (hy : r ≫ b = SSet.const y)
    (g g' : Q ⟶ vertexFiber pointedSpaceProjection y)
    (hg : r ≫ spaceSimplexPointedFamily s = g ≫ vertexFiberι pointedSpaceProjection y)
    (hg' : r ≫ L = g' ≫ vertexFiberι pointedSpaceProjection y) :
    HEq (spaceSimplexPointedFamilyEndpointIso s L hL hL₀ r y hy g g' hg hg')
      (VertexIso.map (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
        (relativeExtensionFiberEndpoint pointedSpaceProjection b i v
          (spaceSimplexPointedFamily_boundary s) r y hy)) :=
  vertexIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories.F2
