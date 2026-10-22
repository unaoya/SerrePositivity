module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTrianglePost
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCoefficientCompositionPrisms
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModuleDerivedFamilyEvaluation

/-! 左右の実 augmentation の native 合成 prism 自身から作る、具体的な導来三角形族。 -/
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

def dgGluingCanonicalDerivedLeftCoefficientTriangleFamily (X Y : DGGluingObject R C D M) :=
  dgGluingDGCompositionTriangleFamilyPost R (RightModule R C)
    (dgGluingNativeLeftCoefficientInput R C D M X Y)
    (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M Y)))
    (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))

def dgGluingCanonicalDerivedRightCoefficientTriangleFamily (X Y : DGGluingObject R C D M) :=
  dgGluingDGCompositionTriangleFamilyPost R (RightModule R C)
    (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M X)))
    (dgGluingNativeRightCoefficientInput R C D M X Y)
    (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))

lemma dgGluingCanonicalDerivedLeftCoefficientTriangleFamily_two (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingCanonicalDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (dgGluingNativeLeftCoefficientInput R C D M X Y)) := by
  rw [dgGluingCanonicalDerivedLeftCoefficientTriangleFamily,
    dgGluingDGCompositionTriangleFamilyPost_two]
  rfl

lemma dgGluingCanonicalDerivedLeftCoefficientTriangleFamily_zero (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingCanonicalDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (SSet.const (pinchedClosedVertex R (RightModule R C)
          (dgGluingAugmentation R C D M Y)))) := by
  rw [dgGluingCanonicalDerivedLeftCoefficientTriangleFamily,
    dgGluingDGCompositionTriangleFamilyPost_zero]
  rfl

lemma dgGluingCanonicalDerivedLeftCoefficientTriangleFamily_one (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingCanonicalDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom)) := by
  rw [dgGluingCanonicalDerivedLeftCoefficientTriangleFamily,
    dgGluingDGCompositionTriangleFamilyPost_one,
    dgGluingNativeLeftCoefficientComposition R C D M X Y]
  rfl

lemma dgGluingCanonicalDerivedRightCoefficientTriangleFamily_two (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingCanonicalDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (SSet.const (pinchedClosedVertex R (RightModule R C)
          (dgGluingAugmentation R C D M X)))) := by
  rw [dgGluingCanonicalDerivedRightCoefficientTriangleFamily,
    dgGluingDGCompositionTriangleFamilyPost_two]
  rfl

lemma dgGluingCanonicalDerivedRightCoefficientTriangleFamily_zero (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingCanonicalDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (dgGluingNativeRightCoefficientInput R C D M X Y)) := by
  rw [dgGluingCanonicalDerivedRightCoefficientTriangleFamily,
    dgGluingDGCompositionTriangleFamilyPost_zero]
  rfl

lemma dgGluingCanonicalDerivedRightCoefficientTriangleFamily_one (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingCanonicalDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom)) := by
  rw [dgGluingCanonicalDerivedRightCoefficientTriangleFamily,
    dgGluingDGCompositionTriangleFamilyPost_one,
    dgGluingNativeRightCoefficientComposition R C D M X Y]
  rfl

end SerrePositivity.InfinityCategories
