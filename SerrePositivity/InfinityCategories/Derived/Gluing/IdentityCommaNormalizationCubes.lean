module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaAugmentationSliceCube
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizationPrisms

/-! 標準閉射による実正規化三角形へ、元 augmentation を適用した二つの全三次元族。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => dgGluingIdentityCommaObject R E Y.source

def dgGluingIdentityCommaPreNormalizeCube :=
  dgGluingCommaAugmentationSliceCube R E E (DGFunctor.id E) Y
    (dgGluingIdentityCommaPreNormalizePrism R E X Y f)

def dgGluingIdentityCommaPostNormalizeCube :=
  dgGluingCommaAugmentationSliceCube R E E (DGFunctor.id E) NY
    (dgGluingIdentityCommaPostNormalizePrism R E X Y f)

lemma dgGluingIdentityCommaPreNormalizeCube_zero :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 K)) ≫
        dgGluingIdentityCommaPreNormalizeCube R E X Y f =
      (Δ[1] ◁ (rightMappingSpacePrism K ≫ sliceOverUncurry
        (f ≫ pinchedHomChainMap (D := Q) (E := Q)
          (dgGluingIdentityCommaPreNormalizeHom R E X Y) ≫ dgPinchedHomSlice R Q NX Y))) ≫
            dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingIdentityCommaPreNormalizeCube, dgGluingCommaAugmentationSliceCube_inner,
    dgGluingIdentityCommaPreNormalizePrism_zero]

lemma dgGluingIdentityCommaPreNormalizeCube_one :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 K)) ≫
        dgGluingIdentityCommaPreNormalizeCube R E X Y f =
      (Δ[1] ◁ (rightMappingSpacePrism K ≫
        sliceOverUncurry (f ≫ dgPinchedHomSlice R Q X Y))) ≫
          dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingIdentityCommaPreNormalizeCube, dgGluingCommaAugmentationSliceCube_inner,
    dgGluingIdentityCommaPreNormalizePrism_one]

lemma dgGluingIdentityCommaPostNormalizeCube_zero :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 K)) ≫
        dgGluingIdentityCommaPostNormalizeCube R E X Y f =
      (Δ[1] ◁ (rightMappingSpacePrism K ≫ sliceOverUncurry
        (f ≫ pinchedHomChainMap (D := Q) (E := Q)
          (dgGluingIdentityCommaNormalizeHom R E X Y) ≫ dgPinchedHomSlice R Q NX NY))) ≫
            dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingIdentityCommaPostNormalizeCube, dgGluingCommaAugmentationSliceCube_inner,
    dgGluingIdentityCommaPostNormalizePrism_zero]

lemma dgGluingIdentityCommaPostNormalizeCube_one :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 K)) ≫
        dgGluingIdentityCommaPostNormalizeCube R E X Y f =
      (Δ[1] ◁ (rightMappingSpacePrism K ≫ sliceOverUncurry
        ((SSet.const (X := K)
          (pinchedClosedVertex R Q (dgGluingIdentityCommaNormalizationClosedOut R E Y))) ≫
            dgPinchedHomSlice R Q Y NY))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingIdentityCommaPostNormalizeCube, dgGluingCommaAugmentationSliceCube_inner,
    dgGluingIdentityCommaPostNormalizePrism_one]

lemma dgGluingIdentityCommaPreNormalizeCube_source :
    (Δ[1] ◁ prismEndpoint 0 _) ≫ dgGluingIdentityCommaPreNormalizeCube R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((SSet.const (X := K)
        (pinchedClosedVertex R Q (dgGluingIdentityCommaNormalizationClosedIn R E X))) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex NX) (Simplex.vertex X))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingIdentityCommaPreNormalizeCube, dgGluingCommaAugmentationSliceCube_source,
    dgGluingIdentityCommaPreNormalizePrism_projection]

lemma dgGluingIdentityCommaPostNormalizeCube_source :
    (Δ[1] ◁ prismEndpoint 0 _) ≫ dgGluingIdentityCommaPostNormalizeCube R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((f ≫ pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaPreNormalizeHom R E X Y)) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex NX) (Simplex.vertex Y))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingIdentityCommaPostNormalizeCube, dgGluingCommaAugmentationSliceCube_source,
    dgGluingIdentityCommaPostNormalizePrism_projection]

end SerrePositivity.InfinityCategories
