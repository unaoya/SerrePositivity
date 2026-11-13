module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningParametrizedTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointedTransformationPointHom
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SpaceEdgeTransportValue

/-!
概要：元の全変換空間の辺のfiber作用を、その同じ辺の点での空間値へ結ぶ。
方針：既存の全パラメータの輸送比較を指定辺で評価し、標準輸送の値比較を合成する。
規約：全fiberからの射の同型であり、fiberの頂点ごとの等式には弱めない。
使われ方：G14 の Yoneda 評価の標的自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の変換辺のpointed fiberへの作用は、同じ辺の点での値と全fiberで可換。 -/
def transformationEdge_pointedFiberValueIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex F) (functorVertex G)) (b : B _⦋0⦌) :
    let s := intervalMappingVertexOfEdge e
    FunctorIso
      (leftUnstraighteningPointedFiberMap F G
          (leftUnstraighteningMappingVertexMap F G s).val
          (leftUnstraighteningMappingVertexMap F G s).property b ≫
        (pointedSpaceFiberValueEquivalence (G.app _ b)).hom)
      ((pointedSpaceFiberValueEquivalence (F.app _ b)).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (spaceInfinityEdgeValue (functorEdgeAt e b))) := by
  let s : (leftUnstraighteningTransformationSpace F G) _⦋0⦌ := intervalMappingVertexOfEdge e
  have h := (leftUnstraighteningMappingFiberHom_parametrizedIso F G b).app s
  rw [pointedTransformationFiberHom_vertex] at h
  have he :
      (intervalMappingPostOfEq (evaluateFunctorAt b) (functorVertex F) (functorVertex G)
        (evaluateFunctorAt_functorVertex b F) (evaluateFunctorAt_functorVertex b G)).app _ s =
        intervalMappingVertexOfEdge (functorEdgeAt e b) := by
    exact intervalMappingPostOfEq_vertex (evaluateFunctorAt b)
      (evaluateFunctorAt_functorVertex b F) (evaluateFunctorAt_functorVertex b G) e
  change VertexIso _ ((parametrizedFiberTransport pointedSpaceProjection (F.app _ b) (G.app _ b)).app _
    ((intervalMappingPostOfEq (evaluateFunctorAt b) (functorVertex F) (functorVertex G)
      (evaluateFunctorAt_functorVertex b F) (evaluateFunctorAt_functorVertex b G)).app _ s)) at h
  rw [he] at h
  have ht := h ≪≫ parametrizedFiberTransport_at_edgeIso pointedSpaceProjection (functorEdgeAt e b)
  change FunctorIso _ (edgeTransport pointedSpaceProjection (functorEdgeAt e b)) at ht
  exact (ht.postcomp (pointedSpaceFiberValueEquivalence (G.app _ b)).hom) ≪≫
    (spaceInfinityEdgeTransportValueIso (functorEdgeAt e b)).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
