module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionInputBoundaryLift
public import SerrePositivity.InfinityCategories.F1.CompositionCorrespondenceDiagonalPullback
public import SerrePositivity.InfinityCategories.F2.KanTensorComplex

/-! 第一辺と対角辺の同時評価は全境界制限の pullback であり、Kan fibration。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)

lemma dgGluingCompositionInputDiagonal_isPullback :
    IsPullback (pullback.fst ((pre (horn 2 1).ι).app X) (composableHomHornMap x g))
      (dgGluingCompositionInputDiagonal x g)
      ((pre (boundary 2).ι).app X) (dgGluingCompositionInputBoundaryMap x g) := by
  refine IsPullback.mk' (dgGluingCompositionInputBoundarySquare x g) ?_ ?_
  · intro T a b h₁ h₀
    exact compositionCorrespondence_hom_ext_triangle x g a b h₁
  · intro T a b h
    exact ⟨dgGluingCompositionInputBoundaryLift x g a b h,
      dgGluingCompositionInputBoundaryLift_triangle x g a b h,
      dgGluingCompositionInputBoundaryLift_inputs x g a b h⟩

lemma dgGluingCompositionInputDiagonal_kanEquivalenceLifting [Quasicategory X] :
    F1B.KanEquivalenceLifting (dgGluingCompositionInputDiagonal x g) := by
  intro A B i hi he
  have : HasLiftingProperty i ((pre (boundary 2).ι).app X) :=
    F1B.kanEquivalenceLifting_pre (boundary 2).ι i hi he
  exact (dgGluingCompositionInputDiagonal_isPullback x g).hasLiftingProperty i

lemma dgGluingCompositionInputDiagonal_fibration [Quasicategory X] :
    Fibration (dgGluingCompositionInputDiagonal x g) := by
  have := compositionCorrespondence_kanComplex x g
  have := F2.kanComplex_tensor (intervalMappingSpace x y) (intervalMappingSpace x z)
  exact fibration_of_kanEquivalenceLifting_of_kanComplex _
    (dgGluingCompositionInputDiagonal_kanEquivalenceLifting x g)

end SerrePositivity.InfinityCategories
