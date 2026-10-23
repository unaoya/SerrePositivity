module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointProductPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconePathSpaceLimit
public import SerrePositivity.InfinityCategories.F2.CatInfinity.KanTensorComplex
public import SerrePositivity.InfinityCategories.F2.CatInfinity.SpaceSquareProjections

/-! 同じ左右 Hom と係数 Hom の実直積を使う、元の差の cocone 空間の ∞ 極限錐。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory CochainComplex
open DifferentialGraded HomotopicalAlgebra SSet.modelCategoryQuillen
open F2
variable {R : Type u} [CommRing R]

def dgGluingComplexPinchedProductKanObject (A B : Complex R) : KanObject.{max u v} :=
  ⟨complexPinchedSpace.{u, v} A ⊗ complexPinchedSpace.{u, v} B, F2.kanComplex_tensor _ _⟩

def dgGluingComplexPathSpaceEndpointPairKanMap (Q : Complex R) :
    dgGluingComplexPinchedKanObject.{u, v} (dgGluingComplexPath Q) ⟶
      dgGluingComplexPinchedProductKanObject.{u, v} Q Q :=
  dgGluingComplexPathSpaceEndpointPair Q

variable {A B Q : Complex R} (f : A ⟶ Q) (g : B ⟶ Q)

def dgGluingComplexActionsProductKanMap :
    dgGluingComplexPinchedProductKanObject.{u, v} A B ⟶
      dgGluingComplexPinchedProductKanObject.{u, v} Q Q :=
  complexPinchedMap.{u, v} f ⊗ₘ complexPinchedMap.{u, v} g

def dgGluingTwoEndpointProductDiagram : AsSmall.{max u v} WalkingCospan ⥤ KanObject.{max u v} :=
  HomotopyLimits.kanPullbackDiagram (dgGluingComplexPathSpaceEndpointPairKanMap.{u, v} Q)
    (dgGluingComplexActionsProductKanMap.{u, v} f g)

def dgGluingTwoEndpointProductCone :
    JoinCone (kanDiagramCoherentNerve (dgGluingTwoEndpointProductDiagram.{u, v} f g)) :=
  F2.spaceSquareCone (K := dgGluingComplexPinchedKanObject.{u, v}
      (mappingCocone (biprod.snd ≫ g - biprod.fst ≫ f)))
    (dgGluingComplexPathSpaceEndpointPairKanMap.{u, v} Q)
    (dgGluingComplexActionsProductKanMap.{u, v} f g)
    (complexPinchedMap.{u, v}
      (dgGluingCoconeTwoEndpointPath (biprod.fst ≫ f) (biprod.snd ≫ g)))
    (lift
      (complexPinchedMap.{u, v}
        (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.fst))
      (complexPinchedMap.{u, v}
        (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.snd)))
    (dgGluingTwoEndpointProduct_isPullback.{u, v} f g)

lemma dgGluingTwoEndpointProductCone_isLimit :
    IsLimitCone (dgGluingTwoEndpointProductCone.{u, v} f g) := by
  let : Fibration
      (show (dgGluingComplexPinchedKanObject.{u, v} (dgGluingComplexPath Q)).obj ⟶
        (dgGluingComplexPinchedProductKanObject.{u, v} Q Q).obj from
        dgGluingComplexPathSpaceEndpointPairKanMap.{u, v} Q) :=
    dgGluingComplexPathSpaceEndpointPair_fibration Q
  exact F2.spaceSquareCone_isLimit _ _ _ _ _

lemma dgGluingTwoEndpointProductCone_vertex :
    (dgGluingTwoEndpointProductCone.{u, v} f g).vertex =
      F2.coherentVertex (dgGluingComplexPinchedKanObject.{u, v}
        (mappingCocone (biprod.snd ≫ g - biprod.fst ≫ f))) :=
  F2.spaceSquareCone_vertex _ _ _ _ _

lemma dgGluingTwoEndpointProductCone_path :
    (nativeConeLeg (dgGluingTwoEndpointProductCone.{u, v} f g)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)))).edge =
      (coherentNerveEdge
        (show dgGluingComplexPinchedKanObject.{u, v}
            (mappingCocone (biprod.snd ≫ g - biprod.fst ≫ f)) ⟶
          dgGluingComplexPinchedKanObject.{u, v} (dgGluingComplexPath Q) from
          complexPinchedMap.{u, v}
            (dgGluingCoconeTwoEndpointPath (biprod.fst ≫ f) (biprod.snd ≫ g)))).edge :=
  F2.spaceSquareCone_left _ _ _ _ _

lemma dgGluingTwoEndpointProductCone_inputs :
    (nativeConeLeg (dgGluingTwoEndpointProductCone.{u, v} f g)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right)))).edge =
      (coherentNerveEdge
        (show dgGluingComplexPinchedKanObject.{u, v}
            (mappingCocone (biprod.snd ≫ g - biprod.fst ≫ f)) ⟶
          dgGluingComplexPinchedProductKanObject.{u, v} A B from
          lift
            (complexPinchedMap.{u, v}
              (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.fst))
            (complexPinchedMap.{u, v}
              (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.snd)))).edge :=
  F2.spaceSquareCone_right _ _ _ _ _

end SerrePositivity.InfinityCategories
