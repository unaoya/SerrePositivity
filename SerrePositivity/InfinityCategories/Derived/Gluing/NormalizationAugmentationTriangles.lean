module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationCubeIntervalFaces
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizationPrisms
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaAugmentationSliceCube
public import SerrePositivity.InfinityCategories.Derived.Gluing.SlicePrismTriangleEndpoints

/-! # augmentation による正規化合成三角形の全 prism

概要：前後の正規化を実合成三角形として扱い、augmentation の全区間族を保持する。
方針：slice prism を二単体へ展開してから、元 augmentation を後合成する。
規約：側面も元の標準合成三角形であり、Small 仮定は課さない。
使われ方：共有面と二つの側面を含む相対貼り合わせの構成。
-/
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

/-- 概要：前正規化の標準合成三角形へ augmentation を適用する。
方針：同じ閉前合成 prism の二単体表示を使う。
規約：元の全 Hom 入力を保持する。使われ方：元面・共有面・始側面を結ぶ prism。 -/
def dgGluingPreNormalizeAugmentationTriangle :=
  (Δ[1] ◁ dgGluingSlicePrismTriangle (dgGluingIdentityCommaPreNormalizePrism R E X Y f)) ≫
    dgGluingCommaAugmentationPrism R E E (DGFunctor.id E)

/-- 概要：後正規化の標準合成三角形へ augmentation を適用する。
方針：同じ閉後合成 prism の二単体表示を使う。
規約：元の全 Hom 入力を保持する。使われ方：共有面・係数面・終側面を結ぶ prism。 -/
def dgGluingPostNormalizeAugmentationTriangle :=
  (Δ[1] ◁ dgGluingSlicePrismTriangle (dgGluingIdentityCommaPostNormalizePrism R E X Y f)) ≫
    dgGluingCommaAugmentationPrism R E E (DGFunctor.id E)

lemma dgGluingPreNormalizeAugmentationTriangle_original :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
        dgGluingPreNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
        (X := dgNerve R Q) (Simplex.vertex X) (Simplex.vertex Y))) ≫
          dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingPreNormalizeAugmentationTriangle, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingSlicePrismTriangle_zero, dgGluingIdentityCommaPreNormalizePrism_one]
  rw [dgGluingPinchedSliceEvaluation]

lemma dgGluingPreNormalizeAugmentationTriangle_shared :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫
        dgGluingPreNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((f ≫ pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaPreNormalizeHom R E X Y)) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex NX) (Simplex.vertex Y))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingPreNormalizeAugmentationTriangle, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingSlicePrismTriangle_one, dgGluingIdentityCommaPreNormalizePrism_zero,
    ← Category.assoc f, dgGluingPinchedSliceEvaluation]

lemma dgGluingPreNormalizeAugmentationTriangle_side :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫
        dgGluingPreNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((SSet.const (X := K)
        (pinchedClosedVertex R Q (dgGluingIdentityCommaNormalizationClosedIn R E X))) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex NX) (Simplex.vertex X))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingPreNormalizeAugmentationTriangle, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingSlicePrismTriangle_front, dgGluingIdentityCommaPreNormalizePrism_projection]

lemma dgGluingPostNormalizeAugmentationTriangle_shared :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫
        dgGluingPostNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫
        dgGluingPreNormalizeAugmentationTriangle R E X Y f := by
  rw [dgGluingPostNormalizeAugmentationTriangle, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingSlicePrismTriangle_front, dgGluingIdentityCommaPostNormalizePrism_projection,
    dgGluingPreNormalizeAugmentationTriangle_shared]

lemma dgGluingPostNormalizeAugmentationTriangle_normalized :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫
        dgGluingPostNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((f ≫ pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaNormalizeHom R E X Y)) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex NX) (Simplex.vertex NY))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingPostNormalizeAugmentationTriangle, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingSlicePrismTriangle_one, dgGluingIdentityCommaPostNormalizePrism_zero,
    ← Category.assoc f, dgGluingPinchedSliceEvaluation]

lemma dgGluingPostNormalizeAugmentationTriangle_side :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
        dgGluingPostNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((SSet.const (X := K)
        (pinchedClosedVertex R Q (dgGluingIdentityCommaNormalizationClosedOut R E Y))) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex Y) (Simplex.vertex NY))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingPostNormalizeAugmentationTriangle, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingSlicePrismTriangle_zero, dgGluingIdentityCommaPostNormalizePrism_one,
    dgGluingPinchedSliceEvaluation]

lemma dgGluingAugmentationTriangle_cube_pre_original :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
        dgGluingPreNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 K)) ≫
        dgGluingIdentityCommaPreNormalizeCube R E X Y f := by
  rw [dgGluingPreNormalizeAugmentationTriangle_original,
    dgGluingIdentityCommaPreNormalizeCube_interval_one]

lemma dgGluingAugmentationTriangle_cube_pre_shared :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫
        dgGluingPreNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 K)) ≫
        dgGluingIdentityCommaPreNormalizeCube R E X Y f := by
  rw [dgGluingPreNormalizeAugmentationTriangle_shared,
    dgGluingIdentityCommaPreNormalizeCube_interval_zero]

lemma dgGluingAugmentationTriangle_cube_post_normalized :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫
        dgGluingPostNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 K)) ≫
        dgGluingIdentityCommaPostNormalizeCube R E X Y f := by
  rw [dgGluingPostNormalizeAugmentationTriangle_normalized,
    dgGluingIdentityCommaPostNormalizeCube_interval_zero]

lemma dgGluingAugmentationTriangle_cube_post_side :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
        dgGluingPostNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 K)) ≫
        dgGluingIdentityCommaPostNormalizeCube R E X Y f := by
  rw [dgGluingPostNormalizeAugmentationTriangle_side,
    dgGluingIdentityCommaPostNormalizeCube_interval_one]

lemma dgGluingAugmentationTriangle_cube_pre_side :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫
        dgGluingPreNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ prismEndpoint 0 _) ≫
        dgGluingIdentityCommaPreNormalizeCube R E X Y f := by
  rw [dgGluingPreNormalizeAugmentationTriangle_side, dgGluingIdentityCommaPreNormalizeCube_source]

lemma dgGluingAugmentationTriangle_cube_post_shared :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫
        dgGluingPostNormalizeAugmentationTriangle R E X Y f =
      (Δ[1] ◁ prismEndpoint 0 _) ≫
        dgGluingIdentityCommaPostNormalizeCube R E X Y f := by
  rw [dgGluingPostNormalizeAugmentationTriangle_shared,
    dgGluingPreNormalizeAugmentationTriangle_shared, dgGluingIdentityCommaPostNormalizeCube_source]

end SerrePositivity.InfinityCategories
