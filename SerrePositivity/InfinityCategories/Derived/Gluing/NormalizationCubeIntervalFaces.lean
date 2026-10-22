module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizationCubes

/-! 正規化 cube の二端面は、同じ元 pinched Hom 族の全区間表示へ augmentation を適用した族。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial

lemma dgGluingPinchedSliceEvaluation (R : Type u) [CommRing R]
    (D : Type v) [DGCategory R D] {K : SSet.{max u v}} {x y : D}
    (f : K ⟶ DGNerve.pinchedHom R D x y) :
    rightMappingSpacePrism K ≫ sliceOverUncurry (f ≫ dgPinchedHomSlice R D x y) =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
        (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)) := by
  rw [pinchedHomToIntervalMappingSpace_uncurry]
  rfl

variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => dgGluingIdentityCommaObject R E Y.source

lemma dgGluingIdentityCommaPreNormalizeCube_interval_zero :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 K)) ≫
        dgGluingIdentityCommaPreNormalizeCube R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((f ≫ pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaPreNormalizeHom R E X Y)) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex NX) (Simplex.vertex Y))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingIdentityCommaPreNormalizeCube_zero, ← Category.assoc f,
    dgGluingPinchedSliceEvaluation]

lemma dgGluingIdentityCommaPreNormalizeCube_interval_one :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 K)) ≫
        dgGluingIdentityCommaPreNormalizeCube R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
        (X := dgNerve R Q) (Simplex.vertex X) (Simplex.vertex Y))) ≫
          dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingIdentityCommaPreNormalizeCube_one, dgGluingPinchedSliceEvaluation]

lemma dgGluingIdentityCommaPostNormalizeCube_interval_zero :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 K)) ≫
        dgGluingIdentityCommaPostNormalizeCube R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((f ≫ pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaNormalizeHom R E X Y)) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex NX) (Simplex.vertex NY))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingIdentityCommaPostNormalizeCube_zero, ← Category.assoc f,
    dgGluingPinchedSliceEvaluation]

lemma dgGluingIdentityCommaPostNormalizeCube_interval_one :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 K)) ≫
        dgGluingIdentityCommaPostNormalizeCube R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((SSet.const (X := K)
        (pinchedClosedVertex R Q (dgGluingIdentityCommaNormalizationClosedOut R E Y))) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex Y) (Simplex.vertex NY))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingIdentityCommaPostNormalizeCube_one, dgGluingPinchedSliceEvaluation]

end SerrePositivity.InfinityCategories
