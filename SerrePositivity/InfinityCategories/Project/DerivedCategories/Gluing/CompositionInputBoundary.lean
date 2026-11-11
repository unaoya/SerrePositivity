module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TriangleBoundaryFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LastFixedCompositionLift

/-! 同じ終辺を固定し、第一辺と対角辺の全入力から三角形境界を構成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X T : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
variable (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z)

lemma dgGluingCompositionInputBoundary_source :
    (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b =
      (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ (horn₂₁.ι₀₁ ▷ T) ≫
        uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap_first, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_face_source,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_face_source]

lemma dgGluingCompositionInputBoundary_target :
    (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b =
      (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ (horn₂₁.ι₁₂ ▷ T) ≫
        uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_face_target, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeFamily_target]

def dgGluingCompositionInputBoundaryFamily : (boundary 2 : SSet.{u}) ⊗ T ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleBoundaryFamily (uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b) (dgGluingCompositionInputBoundary_source x g a b)
    (dgGluingCompositionInputBoundary_target x g a b)

lemma dgGluingCompositionInputBoundaryFamily_horn :
    (Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₂₄ ▷ T) ≫
      dgGluingCompositionInputBoundaryFamily x g a b =
      uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleBoundaryFamily_horn _ _ _ _

lemma dgGluingCompositionInputBoundaryFamily_first :
    (boundary.ι (2 : Fin 3) ▷ T) ≫ dgGluingCompositionInputBoundaryFamily x g a b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a := by
  rw [dgGluingCompositionInputBoundaryFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleBoundaryFamily_face_two,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap_first]

lemma dgGluingCompositionInputBoundaryFamily_diagonal :
    (boundary.ι (1 : Fin 3) ▷ T) ≫ dgGluingCompositionInputBoundaryFamily x g a b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleBoundaryFamily_face_one _ _ _ _

lemma dgGluingCompositionInputBoundaryFamily_last :
    (boundary.ι (0 : Fin 3) ▷ T) ≫ dgGluingCompositionInputBoundaryFamily x g a b =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm g.edge := by
  rw [dgGluingCompositionInputBoundaryFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleBoundaryFamily_face_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap_last]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
