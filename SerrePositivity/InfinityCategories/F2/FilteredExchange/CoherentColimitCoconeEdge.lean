module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitFunctor
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-!
概要：元の比較円柱に余極限関手を適用し、元の全空間余錐間の指定辺を取り出す。
方針：普遍余錐の切断で元の関手辺を写し、頂点の厳密な一致で端点を合わせる。
規約：辺の一次単体を変更しない。使われ方：native な全空間比較との単位の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の円柱から得る、元の全空間余錐間の指定された辺。 -/
def coherentColimitCoconeEdge : SSet.Truncated.Edge
    (X := (truncation 2).obj ((ihom (join ((SSet.uliftFunctor.{u + 1, u}).obj B)
      (Δ[0] : SSet.{u + 1}))).obj SpaceInfinity.{u}))
    (functorVertex (coherentDiagramTotalCocone F).val)
    (functorVertex (coherentDiagramTotalCocone G).val) := by
  let e := (functorEdgeOfSimplicialHomotopy H).map
    ((truncation 2).map (coherentColimitCoconeFunctor B))
  exact ⟨e.edge, e.src_eq.trans (coherentColimitCoconeFunctor_vertex B F),
    e.tgt_eq.trans (coherentColimitCoconeFunctor_vertex B G)⟩

/-- 元の円柱から得る、元の二つの全空間余極限頂点間の指定辺。 -/
def coherentColimitFunctorEdge : SSet.Truncated.Edge (X := (truncation 2).obj SpaceInfinity.{u})
    (coherentDiagramTotalVertex F) (coherentDiagramTotalVertex G) := by
  let e := (functorEdgeOfSimplicialHomotopy H).map
    ((truncation 2).map (coherentColimitFunctor B))
  exact ⟨e.edge, e.src_eq.trans (coherentColimitFunctor_vertex B F),
    e.tgt_eq.trans (coherentColimitFunctor_vertex B G)⟩

/-- 元の全余錐間の指定辺の頂点評価は、元の余極限関手による辺そのもの。 -/
lemma coherentColimitCoconeEdge_apex :
    ((coherentColimitCoconeEdge B H).map ((truncation 2).map (evaluateFunctorAt
      (SSet.yonedaEquiv (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj B)
        (Δ[0] : SSet.{u + 1})))))).edge = (coherentColimitFunctorEdge B H).edge := rfl

end SerrePositivity.InfinityCategories.F2
