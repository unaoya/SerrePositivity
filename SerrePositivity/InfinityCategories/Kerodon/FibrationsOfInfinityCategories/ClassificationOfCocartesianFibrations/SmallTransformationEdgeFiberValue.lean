module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransformationEdgeFiberValueComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallRelativePostNaturality

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



/-- 元の縮小fiberの値比較は、同じ全変換空間の終点射のfiber作用に全自然。 -/
def smallTransformationEdge_fiberValueIso {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex F) (functorVertex G)) (b : B _⦋0⦌) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G)
          (smallLeftUnstraighteningOverMap F G (leftUnstraighteningEdgeLiftMap F G e))
          (smallLeftUnstraighteningOverMap_projection F G _ (leftUnstraighteningEdgeLiftMap_projection F G e)) b) ≫
        (smallLeftUnstraighteningLiftedFiberValueEquivalence G b).hom)
      ((smallLeftUnstraighteningLiftedFiberValueEquivalence F b).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (spaceInfinityEdgeValue (functorEdgeAt e (ULift.up b)))) := by
  have h := (transformationEdge_fiberValueIso F G e (ULift.up b)).precomp
    (smallLeftUnstraighteningFiberIso F b).hom
  simp only [smallLeftUnstraighteningLiftedFiberValueEquivalence, QCatEquivalence.trans,
    qCatEquivalenceOfIso, Category.assoc]
  rw [← Category.assoc, smallLeftUnstraighteningOverMap_fiber_naturality, Category.assoc]
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
