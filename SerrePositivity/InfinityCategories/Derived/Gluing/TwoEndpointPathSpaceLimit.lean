module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointPathSpace
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconePathSpaceLimit
public import SerrePositivity.InfinityCategories.F2.SpaceSquareProjections

/-! 二合成を端点とする同じ cocone 空間を頂点に持つ、実空間の ∞ 極限錐。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex DifferentialGraded HomotopicalAlgebra
open SSet.modelCategoryQuillen
open F2
variable {R : Type u} [CommRing R] {P Q : Complex R} (a b : P ⟶ Q)

def dgGluingTwoEndpointPathSpaceDiagram : AsSmall.{max u v} WalkingCospan ⥤ KanObject.{max u v} :=
  HomotopyLimits.kanPullbackDiagram
    (dgGluingComplexPinchedKanMap.{u, v} (dgGluingComplexPathEndpoints Q))
    (dgGluingComplexPinchedKanMap.{u, v} (biprod.lift a b))

def dgGluingTwoEndpointPathSpaceCone :
    JoinCone (kanDiagramCoherentNerve (dgGluingTwoEndpointPathSpaceDiagram.{u, v} a b)) :=
  F2.spaceSquareCone (K := dgGluingComplexPinchedKanObject.{u, v} (mappingCocone (b - a)))
    (dgGluingComplexPinchedKanMap.{u, v} (dgGluingComplexPathEndpoints Q))
    (dgGluingComplexPinchedKanMap.{u, v} (biprod.lift a b))
    (complexPinchedMap.{u, v} (dgGluingCoconeTwoEndpointPath a b))
    (complexPinchedMap.{u, v} (mappingCocone.fst (b - a)))
    (dgGluingTwoEndpointPathSpace_isPullback.{u, v} a b)

lemma dgGluingTwoEndpointPathSpaceCone_isLimit :
    IsLimitCone (dgGluingTwoEndpointPathSpaceCone.{u, v} a b) := by
  let : Fibration (show (dgGluingComplexPinchedKanObject.{u, v} (dgGluingComplexPath Q)).obj ⟶
      (dgGluingComplexPinchedKanObject.{u, v} (Q ⊞ Q)).obj from
      dgGluingComplexPinchedKanMap.{u, v} (dgGluingComplexPathEndpoints Q)) :=
    dgGluingComplexPathSpaceEndpoints_fibration Q
  exact F2.spaceSquareCone_isLimit _ _ _ _ _

lemma dgGluingTwoEndpointPathSpaceCone_vertex :
    (dgGluingTwoEndpointPathSpaceCone.{u, v} a b).vertex =
      F2.coherentVertex (dgGluingComplexPinchedKanObject.{u, v} (mappingCocone (b - a))) :=
  F2.spaceSquareCone_vertex _ _ _ _ _

lemma dgGluingTwoEndpointPathSpaceCone_path :
    (nativeConeLeg (dgGluingTwoEndpointPathSpaceCone.{u, v} a b)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)))).edge =
      (coherentNerveEdge
        (show dgGluingComplexPinchedKanObject.{u, v} (mappingCocone (b - a)) ⟶
          dgGluingComplexPinchedKanObject.{u, v} (dgGluingComplexPath Q) from
          complexPinchedMap.{u, v} (dgGluingCoconeTwoEndpointPath a b))).edge :=
  F2.spaceSquareCone_left _ _ _ _ _

lemma dgGluingTwoEndpointPathSpaceCone_base :
    (nativeConeLeg (dgGluingTwoEndpointPathSpaceCone.{u, v} a b)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right)))).edge =
      (coherentNerveEdge
        (show dgGluingComplexPinchedKanObject.{u, v} (mappingCocone (b - a)) ⟶
          dgGluingComplexPinchedKanObject.{u, v} P from
          complexPinchedMap.{u, v} (mappingCocone.fst (b - a)))).edge :=
  F2.spaceSquareCone_right _ _ _ _ _

end SerrePositivity.InfinityCategories
