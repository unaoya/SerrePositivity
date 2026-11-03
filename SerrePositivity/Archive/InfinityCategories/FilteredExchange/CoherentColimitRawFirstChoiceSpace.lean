module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUniversalTriangleComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionUniversalPrismEndpoint

/-!
概要：元の第一余極限辺の全初期値を固定した、全実 prism の同じ選択空間を保持する。
方針：同じ実底と初期値を固定する相対延長空間を用いる。
規約：元の指定辺・全係数・初期値を保持。使われ方：第一辺を動かす全三角形の族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
local notation "β" => fst Δ[1] K ≫ SSet.yonedaEquiv.symm
  (SSet.Truncated.Edge.edge (coherentColimitFunctorEdge B a))
local notation "v" => f ≫ vertexFiberι pointedSpaceProjection
  (JoinCocone.vertex (coherentDiagramTotalCocone F))

include f

/-- 元の実第一辺の底と固定初期値は、元の同じ普遍 prism の始点で整合する。 -/
lemma coherentColimitRawFirstChoice_initial_base :
    v ≫ pointedSpaceProjection = prismEndpoint 0 K ≫ β := by
  rw [← coherentColimitRawTransportPointPrism_start B a f, Category.assoc,
    coherentColimitRawTransportPointPrism_projection]

/-- 元の第一辺の実終点の底は、同じ元の中間余錐頂点で厳密に一定。 -/
lemma coherentColimitRawFirstChoice_final_base :
    prismEndpoint 1 K ≫ β = SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone G)) := by
  rw [← coherentColimitRawTransportPointPrism_projection B a f, ← Category.assoc,
    coherentColimitRawTransportPointPrism_finish, Category.assoc, vertexFiberι_comp,
    SSet.comp_const]

/-- 元の指定第一辺と全初期値を固定する、同じ全実 prism の選択空間。 -/
def coherentColimitRawFirstChoiceSpace : SSet.{u + 1} :=
  relativeFunctorExtensionSpace pointedSpaceProjection β (prismEndpoint 0 K) v
    (coherentColimitRawFirstChoice_initial_base B a f)

/-- 元の第一辺の全持ち上げの選択空間は、同じ初期値固定の可縮な Kan 複体。 -/
lemma coherentColimitRawFirstChoiceSpace_isContractibleKan :
    IsContractibleKan (coherentColimitRawFirstChoiceSpace B a f) :=
  relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection β (prismEndpoint 0 K)
    (prismEndpoint_zero_leftAnodyne K) v (coherentColimitRawFirstChoice_initial_base B a f)

end SerrePositivity.InfinityCategories.F2
