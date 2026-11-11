module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentColimitFunctor
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalObject

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の円柱から得る、元の全空間余錐間の指定された辺。 -/
def coherentColimitCoconeEdge : SSet.Truncated.Edge
    (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj B)
      (Δ[0] : SSet.{u + 1}))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F).val)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone G).val) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeFunctor B))
  exact ⟨e.edge, e.src_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeFunctor_vertex B F),
    e.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeFunctor_vertex B G)⟩

/-- 元の円柱から得る、元の二つの全空間余極限頂点間の指定辺。 -/
def coherentColimitFunctorEdge : SSet.Truncated.Edge (X := (truncation 2).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex F) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex G) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitFunctor B))
  exact ⟨e.edge, e.src_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitFunctor_vertex B F),
    e.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitFunctor_vertex B G)⟩

/-- 元の全余錐間の指定辺の頂点評価は、元の余極限関手による辺そのもの。 -/
lemma coherentColimitCoconeEdge_apex :
    ((coherentColimitCoconeEdge B H).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((SSet.uliftFunctor.{u + 1, u}).obj B)
        (Δ[0] : SSet.{u + 1})))))).edge = (coherentColimitFunctorEdge B H).edge := rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
