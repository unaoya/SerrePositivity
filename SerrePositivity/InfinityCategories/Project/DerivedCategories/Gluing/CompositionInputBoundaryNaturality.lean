module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CompositionInputBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TriangleBoundaryFamilyExt

/-! 同じ境界図式の全パラメーター自然性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X T U : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
variable (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z)

lemma dgGluingCompositionInputBoundaryFamily_natural (k : U ⟶ T) :
    ((boundary 2 : SSet.{u}) ◁ k) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily x g a b =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily x g (k ≫ a) (k ≫ b) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleBoundaryFamily_hom_ext
  · rw [← Category.assoc, ← whisker_exchange, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily_horn,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily_horn, ← uncurry_natural_left, Category.assoc]
  · rw [← Category.assoc, ← whisker_exchange, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily_diagonal,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily_diagonal, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

def dgGluingCompositionInputBoundaryMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z ⟶ (ihom (boundary 2 : SSet.{u})).obj X :=
  curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily x g (fst _ _) (snd _ _))

lemma dgGluingCompositionInputBoundaryMap_uncurry
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z) :
    uncurry (k ≫ dgGluingCompositionInputBoundaryMap x g) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily x g (k ≫ fst _ _) (k ≫ snd _ _) := by
  rw [uncurry_natural_left, dgGluingCompositionInputBoundaryMap, uncurry_curry,
    dgGluingCompositionInputBoundaryFamily_natural]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
