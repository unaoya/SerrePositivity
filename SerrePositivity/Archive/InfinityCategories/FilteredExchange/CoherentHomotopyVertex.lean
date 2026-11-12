module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorUnitFamilyDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：元の空間値の比較円柱を、同じ辺と全図式を持つ coherent な変換頂点にする。
方針：実際の関手辺と区間写像空間の頂点の全単射を使う。
規約：辺を選び直さない。使われ方：部分極限の比較円柱を既存の cospan 比較へ接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元のホモトピーの関手辺そのものを coherent な変換頂点として表示する。 -/
def coherentVertexOfHomotopy : (leftUnstraighteningTransformationSpace F G) _⦋0⦌ :=
  intervalMappingVertexOfEdge (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy H))

/-- 元の coherent 頂点を辺へ戻すと、元の円柱の関手辺そのもの。 -/
lemma coherentVertexOfHomotopy_edge :
    (intervalMappingEdgeOfVertex (coherentVertexOfHomotopy H)).edge =
      (functorEdgeOfSimplicialHomotopy H).edge := by
  exact congrArg SSet.Edge.edge
    ((intervalMappingEdgeVertexEquiv (functorVertex F) (functorVertex G)).symm_apply_apply
      (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy H)))

/-- 元の変換頂点の全図式は、元の円柱の curry の一点パラメータ付き評価。 -/
lemma coherentVertexOfHomotopy_familyDiagram :
    coherentTransformationFamilyDiagram (SSet.const (coherentVertexOfHomotopy H)) =
      functorUnitFamilyDiagram (curry H.h) := by
  unfold coherentTransformationFamilyDiagram functorUnitFamilyDiagram intervalMappingUncurry
  rw [SSet.const_comp]
  change _ ≫ functorParameterizedPrism (uncurry (SSet.const
    (functorVertex (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h)))))) = _
  rw [Equiv.symm_apply_apply, uncurry_const_functorVertex]

end SerrePositivity.InfinityCategories.F2
