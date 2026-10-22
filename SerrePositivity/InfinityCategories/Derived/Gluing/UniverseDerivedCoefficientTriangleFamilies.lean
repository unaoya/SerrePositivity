module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModuleDerivedCoefficientTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleDerivedSimplexFamilies

/-! 同じ導来二単体族を、元の Hom 複体と全三辺を保って共通宇宙へ移す。 -/
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

def dgGluingUniverseDerivedLeftCoefficientTriangleFamily (X Y : DGGluingObject R C D M) :=
  dgGluingUniverseModuleDerivedSimplexFamily.{u, v, w} R C
    (homObject R C X.left Y.left) 2 (dgGluingModuleDerivedLeftCoefficientTriangleFamily R C D M X Y)

def dgGluingUniverseDerivedRightCoefficientTriangleFamily (X Y : DGGluingObject R C D M) :=
  dgGluingUniverseModuleDerivedSimplexFamily.{u, v, w} R C
    (homObject R D X.right Y.right) 2
    (dgGluingModuleDerivedRightCoefficientTriangleFamily R C D M X Y)

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_zero (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M Y)))) :=
by
  rw [dgGluingUniverseDerivedLeftCoefficientTriangleFamily,
    dgGluingUniverseModuleDerivedSimplexFamily_face,
    dgGluingModuleDerivedLeftCoefficientTriangleFamily_zero R C D M X Y]
  exact dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_one (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom)) :=
by
  rw [dgGluingUniverseDerivedLeftCoefficientTriangleFamily,
    dgGluingUniverseModuleDerivedSimplexFamily_face,
    dgGluingModuleDerivedLeftCoefficientTriangleFamily_one R C D M X Y]
  exact dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_two (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (dgGluingNativeLeftCoefficientInput R C D M X Y)) :=
by
  rw [dgGluingUniverseDerivedLeftCoefficientTriangleFamily,
    dgGluingUniverseModuleDerivedSimplexFamily_face,
    dgGluingModuleDerivedLeftCoefficientTriangleFamily_two R C D M X Y]
  exact dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_zero (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (dgGluingNativeRightCoefficientInput R C D M X Y)) :=
by
  rw [dgGluingUniverseDerivedRightCoefficientTriangleFamily,
    dgGluingUniverseModuleDerivedSimplexFamily_face,
    dgGluingModuleDerivedRightCoefficientTriangleFamily_zero R C D M X Y]
  exact dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_one (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom)) :=
by
  rw [dgGluingUniverseDerivedRightCoefficientTriangleFamily,
    dgGluingUniverseModuleDerivedSimplexFamily_face,
    dgGluingModuleDerivedRightCoefficientTriangleFamily_one R C D M X Y]
  exact dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_two (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M X)))) :=
by
  rw [dgGluingUniverseDerivedRightCoefficientTriangleFamily,
    dgGluingUniverseModuleDerivedSimplexFamily_face,
    dgGluingModuleDerivedRightCoefficientTriangleFamily_two R C D M X Y]
  exact dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

end SerrePositivity.InfinityCategories
