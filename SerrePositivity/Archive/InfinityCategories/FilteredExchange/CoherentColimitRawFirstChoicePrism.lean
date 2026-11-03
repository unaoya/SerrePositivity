module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceSpace

/-!
概要：元の第一辺の全選択空間上の普遍 prism と全 fiber 終点を保持する。
方針：元の相対延長の全評価を使い、同じ全初期値・実終点・底を回収する。
規約：選択を頂点へ制限しない。使われ方：全最初辺の終点への最後辺普遍輸送の適用。
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
local notation "Q" => coherentColimitRawFirstChoiceSpace B a f
local notation "hv" => coherentColimitRawFirstChoice_initial_base B a f
local notation "hz" => coherentColimitRawFirstChoice_final_base B a f

/-- 元の全第一辺選択における、同じ元の全実 prism の普遍評価。 -/
def coherentColimitRawFirstChoicePrism : (Δ[1] : SSet.{u + 1}) ⊗ (K ⊗ Q) ⟶
    PointedSpaceInfinity.{u} := relativeExtensionUniversalPrism pointedSpaceProjection β v hv

/-- 元の全第一辺の実 fiber 終点を、一つの同じ全射として保持する。 -/
def coherentColimitRawFirstChoiceEndpoint : K ⊗ Q ⟶
    vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone G)) :=
  relativeExtensionUniversalPrismEndpoint pointedSpaceProjection β v hv _ hz

/-- 元の全第一辺の普遍実 prism は、元の同じ全初期値を保持する。 -/
lemma coherentColimitRawFirstChoicePrism_start :
    prismEndpoint 0 (K ⊗ Q) ≫ coherentColimitRawFirstChoicePrism B a f = fst K Q ≫ v :=
  relativeExtensionUniversalPrism_start pointedSpaceProjection β v hv

/-- 元の全第一辺の普遍実 prism の底は、同じ指定第一辺を全選択で引き戻したもの。 -/
lemma coherentColimitRawFirstChoicePrism_projection :
    coherentColimitRawFirstChoicePrism B a f ≫ pointedSpaceProjection =
      fst (Δ[1] : SSet.{u + 1}) (K ⊗ Q) ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge := by
  rw [coherentColimitRawFirstChoicePrism, relativeExtensionUniversalPrism_projection,
    ← Category.assoc, whiskerLeft_fst]
  rfl

/-- 元の全第一辺の実終点は、同じ全 fiber 終点射の包含そのもの。 -/
lemma coherentColimitRawFirstChoicePrism_finish :
    prismEndpoint 1 (K ⊗ Q) ≫ coherentColimitRawFirstChoicePrism B a f =
      coherentColimitRawFirstChoiceEndpoint B a f ≫
        vertexFiberι pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone G)) :=
  relativeExtensionUniversalPrism_finish pointedSpaceProjection β v hv _ hz

end SerrePositivity.InfinityCategories.F2
