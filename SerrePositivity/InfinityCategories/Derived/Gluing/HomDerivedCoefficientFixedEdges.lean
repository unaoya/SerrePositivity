module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleDerivedClosedFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedAugmentationArrowDiagram

/-! 元の Hom 上の二三角形は、主比較の同じ実 augmentation を固定辺として持つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_fixed
    (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      fst _ _ ≫ dgGluingDerivedAugmentationArrowDiagram R C D M Y := by
  rw [dgGluingUniverseDerivedLeftCoefficientTriangleFamily_zero R C D M X Y]
  exact dgGluingUniverseModuleDerivedFamilyInterval_closed.{u, v, w} R C
    (homObject R C X.left Y.left) (dgGluingAugmentation R C D M Y)

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_fixed
    (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      fst _ _ ≫ dgGluingDerivedAugmentationArrowDiagram R C D M X := by
  rw [dgGluingUniverseDerivedRightCoefficientTriangleFamily_two R C D M X Y]
  exact dgGluingUniverseModuleDerivedFamilyInterval_closed.{u, v, w} R C
    (homObject R D X.right Y.right) (dgGluingAugmentation R C D M X)

lemma dgGluingHomDerivedLeftCoefficientTriangle_fixed (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫ dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y =
      fst _ _ ≫ dgGluingDerivedAugmentationArrowDiagram R C D M Y := by
  rw [dgGluingHomDerivedLeftCoefficientTriangle, ← Category.assoc, ← whisker_exchange,
    Category.assoc, dgGluingUniverseDerivedLeftCoefficientTriangleFamily_fixed R C D M X Y,
    whiskerLeft_fst_assoc]

lemma dgGluingHomDerivedRightCoefficientTriangle_fixed (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫ dgGluingHomDerivedRightCoefficientTriangle R C D M X Y =
      fst _ _ ≫ dgGluingDerivedAugmentationArrowDiagram R C D M X := by
  rw [dgGluingHomDerivedRightCoefficientTriangle, ← Category.assoc, ← whisker_exchange,
    Category.assoc, dgGluingUniverseDerivedRightCoefficientTriangleFamily_fixed R C D M X Y,
    whiskerLeft_fst_assoc]

end SerrePositivity.InfinityCategories
