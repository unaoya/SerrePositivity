module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionTriangleEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModuleDerivedFamilyEvaluation

/-! 導来 augmentation の指定三辺を持つ三角形を、実二単体族として供給する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingModuleDerivedLeftCoefficientTriangleFamily (X Y : DGGluingObject R C D M) :=
  dgGluingCompositionTriangleEvaluation (dgGluingModuleDerivedLeftCoefficientTriangle R C D M X Y)

def dgGluingModuleDerivedRightCoefficientTriangleFamily (X Y : DGGluingObject R C D M) :=
  dgGluingCompositionTriangleEvaluation (dgGluingModuleDerivedRightCoefficientTriangle R C D M X Y)

lemma dgGluingModuleDerivedLeftCoefficientTriangleFamily_zero (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M Y)))) :=
  (dgGluingCompositionTriangleEvaluation_zero _).trans
    (dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

lemma dgGluingModuleDerivedLeftCoefficientTriangleFamily_one (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom)) :=
  (dgGluingCompositionTriangleEvaluation_one _).trans
    (dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

lemma dgGluingModuleDerivedLeftCoefficientTriangleFamily_two (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (dgGluingNativeLeftCoefficientInput R C D M X Y)) :=
  (dgGluingCompositionTriangleEvaluation_two _).trans
    (dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

lemma dgGluingModuleDerivedRightCoefficientTriangleFamily_zero (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (dgGluingNativeRightCoefficientInput R C D M X Y)) :=
  (dgGluingCompositionTriangleEvaluation_zero _).trans
    (dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

lemma dgGluingModuleDerivedRightCoefficientTriangleFamily_one (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom)) :=
  (dgGluingCompositionTriangleEvaluation_one _).trans
    (dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

lemma dgGluingModuleDerivedRightCoefficientTriangleFamily_two (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingModuleDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M X)))) :=
  (dgGluingCompositionTriangleEvaluation_two _).trans
    (dgGluingModuleDerivedFamilyHomotopy_evaluate R C _)

end SerrePositivity.InfinityCategories
