module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomDerivedCoefficientTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseModuleDerivedClosedFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Augmentations.DerivedAugmentationArrowDiagram

/-! 元の Hom 上の二三角形は、主比較の同じ実 augmentation を固定辺として持つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_fixed
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationArrowDiagram R C D M Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedLeftCoefficientTriangleFamily_zero R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval_closed.{u, v, w} R C
    (homObject R C X.left Y.left) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y)

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_fixed
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationArrowDiagram R C D M X := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedRightCoefficientTriangleFamily_two R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval_closed.{u, v, w} R C
    (homObject R D X.right Y.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)

lemma dgGluingHomDerivedLeftCoefficientTriangle_fixed (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationArrowDiagram R C D M Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLeftCoefficientTriangle, ← Category.assoc, ← whisker_exchange,
    Category.assoc, dgGluingUniverseDerivedLeftCoefficientTriangleFamily_fixed R C D M X Y,
    whiskerLeft_fst_assoc]

lemma dgGluingHomDerivedRightCoefficientTriangle_fixed (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedRightCoefficientTriangle R C D M X Y =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationArrowDiagram R C D M X := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedRightCoefficientTriangle, ← Category.assoc, ← whisker_exchange,
    Category.assoc, dgGluingUniverseDerivedRightCoefficientTriangleFamily_fixed R C D M X Y,
    whiskerLeft_fst_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
