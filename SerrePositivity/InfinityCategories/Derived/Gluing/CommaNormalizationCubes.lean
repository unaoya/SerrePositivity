module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationCubeIntervalFaces
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImageAugmentationPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaNormalizedCochainLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedIntervalImage

/-! 元 comma の全 Hom 族を保持し、実正規化 cube の一面を元 augmentation、他面を明示 lift へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [DGCategory R C] [DGCategory R E]
  (F : DGFunctor R C E) (X Y : DGFunctorCommaObject R C E F)
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R (DGFunctorCommaObject R C E F) X Y)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "IX" => dgGluingCommaImageObject R C E F X
local notation "IY" => dgGluingCommaImageObject R C E F Y
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => dgGluingIdentityCommaObject R E (F.obj Y.source)

def dgGluingCommaPreNormalizeCube :=
  dgGluingIdentityCommaPreNormalizeCube R E IX IY
    (f ≫ pinchedHomChainMap (D := DGFunctorCommaObject R C E F) (E := Q)
      (dgGluingCommaImageHomMap R C E F X Y))

def dgGluingCommaPostNormalizeCube :=
  dgGluingIdentityCommaPostNormalizeCube R E IX IY
    (f ≫ pinchedHomChainMap (D := DGFunctorCommaObject R C E F) (E := Q)
      (dgGluingCommaImageHomMap R C E F X Y))

lemma dgGluingCommaPreNormalizeCube_original_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 K)) ≫ dgGluingCommaPreNormalizeCube R C E F X Y f =
      (Δ[1] ◁ intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
        (X := dgNerve R (DGFunctorCommaObject R C E F)) (Simplex.vertex X) (Simplex.vertex Y))) ≫
          dgGluingCommaAugmentationPrism R C E F := by
  have hf := dgGluingFunctorPinchedIntervalImage (dgGluingCommaImageFunctor R C E F) f
  change intervalMappingUncurry ((f ≫ pinchedHomChainMap
      (D := DGFunctorCommaObject R C E F) (E := Q)
      (dgGluingCommaImageHomMap R C E F X Y)) ≫
        pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
          (Simplex.vertex IX) (Simplex.vertex IY)) =
    intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
      (X := dgNerve R (DGFunctorCommaObject R C E F)) (Simplex.vertex X) (Simplex.vertex Y)) ≫
        dgNerve.map (dgGluingCommaImageFunctor R C E F) at hf
  rw [dgGluingCommaPreNormalizeCube, dgGluingIdentityCommaPreNormalizeCube_interval_one,
    hf, whiskerLeft_comp, Category.assoc, dgGluingCommaImageAugmentationPrism R C E F]

lemma dgGluingCommaPostNormalizeCube_normalized_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 K)) ≫ dgGluingCommaPostNormalizeCube R C E F X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((f ≫ pinchedHomChainMap
        (D := DGFunctorCommaObject R C E F) (E := Q)
        (dgGluingCommaNormalizedHom R C E F X Y)) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex NX) (Simplex.vertex NY))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  have hc := pinchedHomChainMap_comp (D := DGFunctorCommaObject R C E F) (E := Q) (T := Q)
    (x := X) (y := Y) (x' := IX) (y' := IY) (x'' := NX) (y'' := NY)
    (dgGluingCommaImageHomMap R C E F X Y) (dgGluingIdentityCommaNormalizeHom R E IX IY)
  have hh : (f ≫ pinchedHomChainMap (D := DGFunctorCommaObject R C E F) (E := Q)
      (dgGluingCommaImageHomMap R C E F X Y)) ≫
        pinchedHomChainMap (D := Q) (E := Q) (dgGluingIdentityCommaNormalizeHom R E IX IY) =
      f ≫ pinchedHomChainMap (D := DGFunctorCommaObject R C E F) (E := Q)
        (dgGluingCommaNormalizedHom R C E F X Y) := by
    rw [Category.assoc, ← hc]
    rfl
  rw [dgGluingCommaPostNormalizeCube, dgGluingIdentityCommaPostNormalizeCube_interval_zero, hh]
  rfl

lemma dgGluingCommaPostNormalizeCube_cochain_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 K)) ≫ dgGluingCommaPostNormalizeCube R C E F X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((f ≫ pinchedHomChainMap
        (D := DGFunctorCommaObject R C E F) (E := Q)
        (dgGluingCochainIdentityCommaLift R E X.replacement (F.obj Y.source) _
          (dgGluingCommaNormalizedReplacement R C E F X Y)
          (dgGluingCommaNormalizedSource R C E F X Y)
          (-dgFunctorCommaPrimitive R C E F X Y)
          (dgGluingCommaNormalizedNegativePrimitive_boundary R C E F X Y))) ≫
            pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
              (Simplex.vertex NX) (Simplex.vertex NY))) ≫
                dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingCommaPostNormalizeCube_normalized_face, dgGluingCommaNormalizedHom_eq_cochainLift]
  rfl

end SerrePositivity.InfinityCategories
