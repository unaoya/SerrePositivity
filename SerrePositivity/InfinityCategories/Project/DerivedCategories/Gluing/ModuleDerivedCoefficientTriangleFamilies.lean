module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CompositionTriangleEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModuleDerivedFamilyEvaluation

/-! 導来 augmentation の指定三辺を持つ三角形を、実二単体族として供給する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingModuleDerivedLeftCoefficientTriangleFamily (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedLeftCoefficientTriangle R C D M X Y)

def dgGluingModuleDerivedRightCoefficientTriangleFamily (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedRightCoefficientTriangle R C D M X Y)

lemma dgGluingModuleDerivedLeftCoefficientTriangleFamily_zero (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedLeftCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyInterval R C
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y)))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation_zero _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

lemma dgGluingModuleDerivedLeftCoefficientTriangleFamily_one (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedLeftCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyInterval R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation_one _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

lemma dgGluingModuleDerivedLeftCoefficientTriangleFamily_two (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedLeftCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyInterval R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientInput R C D M X Y)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation_two _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

lemma dgGluingModuleDerivedRightCoefficientTriangleFamily_zero (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedRightCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyInterval R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientInput R C D M X Y)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation_zero _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

lemma dgGluingModuleDerivedRightCoefficientTriangleFamily_one (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedRightCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyInterval R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation_one _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

lemma dgGluingModuleDerivedRightCoefficientTriangleFamily_two (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedRightCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyInterval R C
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation_two _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
