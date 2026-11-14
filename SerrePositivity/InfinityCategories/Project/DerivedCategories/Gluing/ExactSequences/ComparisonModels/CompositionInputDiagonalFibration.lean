module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.CompositionInputBoundaryLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceDiagonalPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanTensorComplex

/-! 第一辺と対角辺の同時評価は全境界制限の pullback であり、Kan fibration。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)

lemma dgGluingCompositionInputDiagonal_isPullback :
    IsPullback (pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputDiagonal x g)
      ((pre (boundary 2).ι).app X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryMap x g) := by
  refine IsPullback.mk' (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundarySquare x g) ?_ ?_
  · intro T a b h₁ h₀
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence_hom_ext_triangle x g a b h₁
  · intro T a b h
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryLift x g a b h,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryLift_triangle x g a b h,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryLift_inputs x g a b h⟩

lemma dgGluingCompositionInputDiagonal_kanEquivalenceLifting [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputDiagonal x g) := by
  intro A B i hi he
  have : HasLiftingProperty i ((pre (boundary 2).ι).app X) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceLifting_pre (boundary 2).ι i hi he
  exact (dgGluingCompositionInputDiagonal_isPullback x g).hasLiftingProperty i

lemma dgGluingCompositionInputDiagonal_fibration [Quasicategory X] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputDiagonal x g) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence_kanComplex x g
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_kanEquivalenceLifting_of_kanComplex _
    (dgGluingCompositionInputDiagonal_kanEquivalenceLifting x g)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
