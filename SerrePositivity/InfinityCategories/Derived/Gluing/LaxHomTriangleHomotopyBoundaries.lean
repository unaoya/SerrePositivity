module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomTriangleHomotopyFamilies

/-! 二三角形の全時間族は augmentation 固定辺と元 Hom 可変辺を時間方向にも保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingLaxHomFirstTriangleHomotopyFamily_fixed (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ dgGluingLaxHomFirstTriangleHomotopyFamily R C D M X Y =
      fst _ _ ≫ SSet.yonedaEquiv.symm (dgGluingDerivedAugmentationEdge R C D M X).edge := by
  rw [dgGluingLaxHomFirstTriangleHomotopyFamily, dgGluingFamilyAlongHomotopy_face,
    dgGluingDerivedFirstInputTriangleEvaluation_fixed R C D M X Y,
    ← Category.assoc, whiskerLeft_fst]

lemma dgGluingLaxHomLastTriangleHomotopyFamily_fixed (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ dgGluingLaxHomLastTriangleHomotopyFamily R C D M X Y =
      fst _ _ ≫ SSet.yonedaEquiv.symm (dgGluingDerivedAugmentationEdge R C D M Y).edge := by
  rw [dgGluingLaxHomLastTriangleHomotopyFamily, dgGluingFamilyAlongHomotopy_face,
    dgGluingDerivedLastInputTriangleEvaluation_fixed R C D M X Y,
    ← Category.assoc, whiskerLeft_fst]

lemma dgGluingLaxHomFirstTriangleHomotopyFamily_variable (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ dgGluingLaxHomFirstTriangleHomotopyFamily R C D M X Y =
      intervalMappingUncurry
        (fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫
          dgGluingHomDerivedRightCoefficientInput R C D M X Y) := by
  rw [dgGluingLaxHomFirstTriangleHomotopyFamily, dgGluingFamilyAlongHomotopy_face,
    dgGluingDerivedFirstInputTriangleEvaluation_variable R C D M X Y,
    ← intervalMappingUncurry_precomp]
  apply congrArg intervalMappingUncurry
  rw [← Category.assoc, dgGluingLaxHomFirstInputHomotopy_over R C D M X Y, Category.assoc,
    ← dgGluingHomDerivedRightCoefficientInput_raw_factor R C D M X Y]

lemma dgGluingLaxHomLastTriangleHomotopyFamily_variable (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ dgGluingLaxHomLastTriangleHomotopyFamily R C D M X Y =
      intervalMappingUncurry
        (fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫
          dgGluingHomDerivedLeftCoefficientInput R C D M X Y) := by
  rw [dgGluingLaxHomLastTriangleHomotopyFamily, dgGluingFamilyAlongHomotopy_face,
    dgGluingDerivedLastInputTriangleEvaluation_variable R C D M X Y,
    ← intervalMappingUncurry_precomp]
  apply congrArg intervalMappingUncurry
  rw [← Category.assoc, dgGluingLaxHomLastInputHomotopy_over R C D M X Y, Category.assoc,
    ← dgGluingHomDerivedLeftCoefficientInput_raw_factor R C D M X Y]

lemma dgGluingLaxHomFirstTriangleHomotopyFamily_diagonal (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ dgGluingLaxHomFirstTriangleHomotopyFamily R C D M X Y =
      intervalMappingUncurry ((dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingLaxHomFirstTriangleHomotopyFamily, dgGluingFamilyAlongHomotopy_face,
    dgGluingDerivedFirstInputTriangleEvaluation_diagonal R C D M X Y,
    ← intervalMappingUncurry_precomp]

lemma dgGluingLaxHomLastTriangleHomotopyFamily_diagonal (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ dgGluingLaxHomLastTriangleHomotopyFamily R C D M X Y =
      intervalMappingUncurry ((dgGluingLaxHomLastInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingLaxHomLastTriangleHomotopyFamily, dgGluingFamilyAlongHomotopy_face,
    dgGluingDerivedLastInputTriangleEvaluation_diagonal R C D M X Y,
    ← intervalMappingUncurry_precomp]

end SerrePositivity.InfinityCategories
