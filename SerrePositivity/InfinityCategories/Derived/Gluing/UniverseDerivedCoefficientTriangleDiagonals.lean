module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedCoefficientTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedCoefficientActionFamilies

/-! 共通宇宙の同じ二三角形の対角は、canonical な導来係数比較による二作用の像。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_diagonal
    (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
            (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y)) ≫
          dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right ≫
            (dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
              pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingUniverseDerivedLeftCoefficientTriangleFamily_one R C D M X Y,
    dgGluingUniverseModuleDerivedFamilyInterval_coefficient R C D M X.left Y.right
      (dgGluingLeftAction R C D M X Y)]

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_diagonal
    (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
            (complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y)) ≫
          dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right ≫
            (dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
              pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingUniverseDerivedRightCoefficientTriangleFamily_one R C D M X Y,
    dgGluingUniverseModuleDerivedFamilyInterval_coefficient R C D M X.left Y.right
      (dgGluingRightAction R C D M X Y)]

end SerrePositivity.InfinityCategories
