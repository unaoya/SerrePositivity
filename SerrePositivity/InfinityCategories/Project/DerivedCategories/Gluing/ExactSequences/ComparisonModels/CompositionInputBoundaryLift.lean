module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.CompositionInputBoundarySquare

/-! 全境界の一致から、同じ入力と対角を持つ元の合成三角形へ持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X T : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
variable (a : T ⟶ (ihom (Δ[2] : SSet.{u})).obj X)
  (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z)
  (h : a ≫ (pre (boundary 2).ι).app X = b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryMap x g)

include h in
lemma dgGluingCompositionInputBoundaryLift_face (i : Fin 3) :
    (stdSimplex.δ i ▷ T) ≫ uncurry a =
      (boundary.ι i ▷ T) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily x g (b ≫ fst _ _) (b ≫ snd _ _) := by
  have hh := congrArg (fun k => (boundary.ι i ▷ T) ≫ uncurry k) h
  simpa only [uncurry_pre_app, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryMap_uncurry,
    ← Category.assoc, ← comp_whiskerRight, boundary.ι_ι] using hh

def dgGluingCompositionInputBoundaryLift : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x g :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastFixedCompositionLift x g (b ≫ fst _ _) (uncurry a)
    ((dgGluingCompositionInputBoundaryLift_face x g a b h 2).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily_first x g _ _))
    ((dgGluingCompositionInputBoundaryLift_face x g a b h 0).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily_last x g _ _))

lemma dgGluingCompositionInputBoundaryLift_triangle :
    dgGluingCompositionInputBoundaryLift x g a b h ≫
      pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) = a := by
  rw [dgGluingCompositionInputBoundaryLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastFixedCompositionLift_triangle,
    curry_uncurry]

lemma dgGluingCompositionInputBoundaryLift_inputs :
    dgGluingCompositionInputBoundaryLift x g a b h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputDiagonal x g = b := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputDiagonal_first,
      dgGluingCompositionInputBoundaryLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastFixedCompositionLift_first]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputDiagonal_diagonal]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x z
    rw [dgGluingCompositionInputBoundaryLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastFixedCompositionLift_diagonal,
      dgGluingCompositionInputBoundaryLift_face x g a b h 1,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputBoundaryFamily_diagonal]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
