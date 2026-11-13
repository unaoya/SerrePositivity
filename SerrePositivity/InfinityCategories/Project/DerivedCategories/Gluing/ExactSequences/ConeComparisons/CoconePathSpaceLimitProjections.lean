module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ConeComparisons.CoconePathSpaceLimit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceSquareProjections

/-! 空間の ∞ 極限錐の二つの脚は、元の path 写像と cocone 射影の厳密な辺。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded CochainComplex

variable {R : Type u} [CommRing R] {P Q : Complex R} (d : P ⟶ Q)

lemma dgGluingCoconePathSpaceCone_path :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathSpaceCone.{u, v} d)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v} (mappingCocone d) ⟶
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v} (mappingCocone (𝟙 Q)) from
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathMap d))).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone_left _ _ _ _ _

lemma dgGluingCoconePathSpaceCone_base :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathSpaceCone.{u, v} d)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v} (mappingCocone d) ⟶
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedKanObject.{u, v} P from
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (mappingCocone.fst d))).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone_right _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
