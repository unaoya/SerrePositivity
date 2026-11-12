module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TwoEndpointProductPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconePathSpaceLimit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanTensorComplex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceSquareProjections

/-! 同じ左右 Hom と係数 Hom の実直積を使う、元の差の cocone 空間の ∞ 極限錐。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory CochainComplex
open DifferentialGraded HomotopicalAlgebra SSet.modelCategoryQuillen

variable {R : Type u} [CommRing R]

def dgGluingComplexPinchedProductKanObject (A B : Complex R) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{max u v} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} A ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} B, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor _ _⟩

def dgGluingComplexPathSpaceEndpointPairKanMap (Q : Complex R) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q) ⟶
      dgGluingComplexPinchedProductKanObject.{u, v} Q Q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair Q

variable {A B Q : Complex R} (f : A ⟶ Q) (g : B ⟶ Q)

def dgGluingComplexActionsProductKanMap :
    dgGluingComplexPinchedProductKanObject.{u, v} A B ⟶
      dgGluingComplexPinchedProductKanObject.{u, v} Q Q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} f ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} g

def dgGluingTwoEndpointProductDiagram : AsSmall.{max u v} WalkingCospan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram (dgGluingComplexPathSpaceEndpointPairKanMap.{u, v} Q)
    (dgGluingComplexActionsProductKanMap.{u, v} f g)

def dgGluingTwoEndpointProductCone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (dgGluingTwoEndpointProductDiagram.{u, v} f g)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone (K := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v}
      (mappingCocone (biprod.snd ≫ g - biprod.fst ≫ f)))
    (dgGluingComplexPathSpaceEndpointPairKanMap.{u, v} Q)
    (dgGluingComplexActionsProductKanMap.{u, v} f g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath (biprod.fst ≫ f) (biprod.snd ≫ g)))
    (lift
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v}
        (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.fst))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v}
        (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.snd)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTwoEndpointProduct_isPullback.{u, v} f g)

lemma dgGluingTwoEndpointProductCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (dgGluingTwoEndpointProductCone.{u, v} f g) := by
  let : Fibration
      (show (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q)).obj ⟶
        (dgGluingComplexPinchedProductKanObject.{u, v} Q Q).obj from
        dgGluingComplexPathSpaceEndpointPairKanMap.{u, v} Q) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair_fibration Q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone_isLimit _ _ _ _ _

lemma dgGluingTwoEndpointProductCone_vertex :
    (dgGluingTwoEndpointProductCone.{u, v} f g).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v}
        (mappingCocone (biprod.snd ≫ g - biprod.fst ≫ f))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone_vertex _ _ _ _ _

lemma dgGluingTwoEndpointProductCone_path :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (dgGluingTwoEndpointProductCone.{u, v} f g)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v}
            (mappingCocone (biprod.snd ≫ g - biprod.fst ≫ f)) ⟶
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q) from
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v}
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath (biprod.fst ≫ f) (biprod.snd ≫ g)))).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone_left _ _ _ _ _

lemma dgGluingTwoEndpointProductCone_inputs :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (dgGluingTwoEndpointProductCone.{u, v} f g)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v}
            (mappingCocone (biprod.snd ≫ g - biprod.fst ≫ f)) ⟶
          dgGluingComplexPinchedProductKanObject.{u, v} A B from
          lift
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v}
              (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.fst))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v}
              (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.snd)))).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone_right _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
