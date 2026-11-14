module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransformationEdgeFiberValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningEdgeLiftFamily
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


/-- 同じ元の終点射のfiber作用は、元のfiber値比較の下で各点の空間辺の作用に全自然。 -/
def transformationEdge_fiberValueIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex F) (functorVertex G)) (b : B _⦋0⦌) :
    FunctorIso
      (vertexFiberMap (leftUnstraighteningProjection F) (leftUnstraighteningProjection G)
          (leftUnstraighteningEdgeLiftMap F G e) (leftUnstraighteningEdgeLiftMap_projection F G e) b ≫
        (leftUnstraighteningFiberValueEquivalence G b).hom)
      ((leftUnstraighteningFiberValueEquivalence F b).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (spaceInfinityEdgeValue (functorEdgeAt e b))) := by
  let s : (leftUnstraighteningTransformationSpace F G) _⦋0⦌ := intervalMappingVertexOfEdge e
  have hm : (leftUnstraighteningMappingVertexMap F G s).val =
      leftUnstraighteningEdgeLiftMap F G e := by
    apply functorVertex_injective
    exact congrArg Subtype.val ((leftUnstraighteningMappingVertexMap_vertex F G s).trans
      (leftUnstraighteningEdgeLiftMap_vertex F G e))
  dsimp only [s] at hm
  have h := transformationEdge_pointedFiberValueIso F G e b
  dsimp only at h
  have h' := h.precomp (leftUnstraighteningFiberIso F b).hom
  simpa only [hm, leftUnstraighteningPointedFiberMap, leftUnstraighteningFiberValueEquivalence,
    QCatEquivalence.trans, qCatEquivalenceOfIso, Category.assoc, Iso.hom_inv_id_assoc] using h'

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
