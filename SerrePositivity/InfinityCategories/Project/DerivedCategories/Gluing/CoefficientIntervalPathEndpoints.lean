module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoefficientIntervalPathComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TwoEndpointPathProduct
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ArrowEndpointPair

/-! 係数の実区間族への同じ同値は、元の端点対の上の厳密な比較である。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open HomotopicalAlgebra SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R] (Q : Complex R)

lemma dgGluingCoefficientIntervalPathComparison_endpoints :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison.{u, v} Q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair.{u, v} Q := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair,
      Category.assoc, lift_fst]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison_start Q
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair,
      Category.assoc, lift_snd]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison_end Q

lemma dgGluingCoefficientIntervalEndpoints_fibration :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair_restriction]
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  intro A B i hi
  let : HasLiftingProperty i
      ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryι).app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance i hi
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
