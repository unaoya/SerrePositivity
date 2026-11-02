module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberTransport
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransportRepresentation

/-!
概要：元の表現の比較を、同じ pointed space の指定 fiber への実際の射として回収する。
方針：表現の fiber 比較と引き戻し fiber 同型を合成する。
規約：包含後の射は同じ全空間の pointed 写像への制限。
使われ方：元の全余錐の一つの表現から、指定頂点上の同値を取り出す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]

/-- 元の表現の比較が与える、指定頂点上の実 pointed fiber 写像。 -/
def representationPointedFiberMap (R : LeftTransportRepresentation p) (b : B _⦋0⦌) :
    vertexFiber p b ⟶ vertexFiber pointedSpaceProjection (R.diagram.app _ b) :=
  vertexFiberMap p (leftUnstraighteningProjection R.diagram) R.comparison R.over_base b ≫
    (leftUnstraighteningFiberIso R.diagram b).hom

/-- 同じ fiber 写像は、全空間の元の pointed 写像への制限そのもの。 -/
lemma representationPointedFiberMap_ι (R : LeftTransportRepresentation p) (b : B _⦋0⦌) :
    representationPointedFiberMap R b ≫ vertexFiberι pointedSpaceProjection
      (R.diagram.app _ b) = vertexFiberι p b ≫ R.pointedMap := by
  rw [representationPointedFiberMap, Category.assoc, leftUnstraighteningFiberIso_hom_ι,
    ← Category.assoc, vertexFiberMap_ι, Category.assoc]
  rfl

/-- 元の表現の全 fiber 同値性は、同じ実 pointed fiber 写像に成立する。 -/
lemma representationPointedFiberMap_isQCatEquivalence
    (R : LeftTransportRepresentation p) (b : B _⦋0⦌) :
    IsQCatEquivalence (representationPointedFiberMap R b) :=
  (R.fiber_equivalence b).comp
    (qCatEquivalenceOfIso (leftUnstraighteningFiberIso R.diagram b)).isQCatEquivalence

end SerrePositivity.InfinityCategories.F2.Compact
