module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationRawFaces
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeDerivedNormalizationCubes
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeIdentityAugmentationPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniversePinchedIntervalEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSquareComposition

/-! native cube の元 augmentation 面を、正本の同じ全 Hom 区間族・実導来矢印族へ厳密に照合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "Q" => DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (DGFunctor.id (RightModule R C))
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y

def dgGluingNativeHomIntervalEvaluation :=
  dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
    (intervalMappingUncurry (pinchedHomToIntervalMappingSpace
      (X := dgNerve R (DGGluingObject R C D M)) (Simplex.vertex X) (Simplex.vertex Y)))

def dgGluingNativeAugmentationIntervalSquare :=
  (Δ[1] ◁ dgGluingNativeHomIntervalEvaluation R C D M X Y) ≫
    (β_ (Δ[1] : SSet.{max (u + 1) v w})
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (dgNerve R (DGGluingObject R C D M)))).hom ≫ dgGluingUniverseAugmentationPrism R C D M

lemma dgGluingNativePreNormalizeCube_original_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 _)) ≫ dgGluingNativePreNormalizeCube R C D M X Y =
      dgGluingNativeAugmentationIntervalSquare R C D M X Y := by
  let p := intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
    (Simplex.vertex IX) (Simplex.vertex IY))
  have hf : (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y) ≫
      dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1 p =
    dgGluingNativeHomIntervalEvaluation R C D M X Y ≫
      dgGluingUniverseNerveMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
        (dgGluingNativeIdentityCommaFunctor R C D M) :=
    dgGluingUniverseFunctorPinchedInterval
      (dgGluingNativeIdentityCommaFunctor R C D M) X Y
  rw [dgGluingNativePreNormalizeCube, dgGluingNativeNormalizationCube_inner,
    dgGluingNativePreNormalizeRawCube_original_face]
  change (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y)) ≫
    dgGluingUliftSquareFamily.{max (u + 1) v, max (u + 1) v w}
      ((Δ[1] ◁ p) ≫ dgGluingModuleIdentityAugmentationPrism R C) = _
  rw [dgGluingUliftSquareFamily_comp, ← Category.assoc, ← whiskerLeft_comp,
    hf, whiskerLeft_comp, Category.assoc, dgGluingNativeIdentityAugmentationPrism]
  rfl

lemma dgGluingNativeDerivedPreNormalizeCube_original_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 _)) ≫
        dgGluingNativeDerivedPreNormalizeCube R C D M X Y =
      (Δ[1] ◁ dgGluingNativeHomIntervalEvaluation R C D M X Y) ≫
        (β_ (Δ[1] : SSet.{max (u + 1) v w})
          ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (dgNerve R (DGGluingObject R C D M)))).hom ≫
              (dgGluingUniverseDerivedAugmentationHomotopy R C D M).h := by
  rw [dgGluingNativeDerivedPreNormalizeCube, ← Category.assoc,
    dgGluingNativePreNormalizeCube_original_face, dgGluingNativeAugmentationIntervalSquare]
  simp only [Category.assoc]
  rfl

end SerrePositivity.InfinityCategories
