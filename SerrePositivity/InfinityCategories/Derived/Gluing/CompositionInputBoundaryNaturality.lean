module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionInputBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.TriangleBoundaryFamilyExt

/-! 同じ境界図式の全パラメーター自然性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X T U : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
variable (a : T ⟶ intervalMappingSpace x y) (b : T ⟶ intervalMappingSpace x z)

lemma dgGluingCompositionInputBoundaryFamily_natural (k : U ⟶ T) :
    ((boundary 2 : SSet.{u}) ◁ k) ≫ dgGluingCompositionInputBoundaryFamily x g a b =
      dgGluingCompositionInputBoundaryFamily x g (k ≫ a) (k ≫ b) := by
  apply dgGluingTriangleBoundaryFamily_hom_ext
  · rw [← Category.assoc, ← whisker_exchange, Category.assoc,
      dgGluingCompositionInputBoundaryFamily_horn,
      dgGluingCompositionInputBoundaryFamily_horn, ← uncurry_natural_left, Category.assoc]
  · rw [← Category.assoc, ← whisker_exchange, Category.assoc,
      dgGluingCompositionInputBoundaryFamily_diagonal,
      dgGluingCompositionInputBoundaryFamily_diagonal, ← intervalMappingUncurry_precomp]

def dgGluingCompositionInputBoundaryMap :
    intervalMappingSpace x y ⊗ intervalMappingSpace x z ⟶ (ihom (boundary 2 : SSet.{u})).obj X :=
  curry (dgGluingCompositionInputBoundaryFamily x g (fst _ _) (snd _ _))

lemma dgGluingCompositionInputBoundaryMap_uncurry
    (k : T ⟶ intervalMappingSpace x y ⊗ intervalMappingSpace x z) :
    uncurry (k ≫ dgGluingCompositionInputBoundaryMap x g) =
      dgGluingCompositionInputBoundaryFamily x g (k ≫ fst _ _) (k ≫ snd _ _) := by
  rw [uncurry_natural_left, dgGluingCompositionInputBoundaryMap, uncurry_curry,
    dgGluingCompositionInputBoundaryFamily_natural]

end SerrePositivity.InfinityCategories
