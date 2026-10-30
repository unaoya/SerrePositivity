module

public import SerrePositivity.PerfectComplex.TensorTripleCyclicSumPerfect
public import SerrePositivity.PerfectComplex.CochainCyclicThree
public import SerrePositivity.PerfectComplex.ClosedSupportRelations
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent

/-! # The eigenspaces of a cyclic tensor orbit -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
variable (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Align the three tensor rotations with the first tensor complex. -/
def cochainTensorCyclicSumStandardIso : cochainTensorCyclicSum P Q T ≅
    cochainCyclicThree (cochainTensor (cochainTensor P Q) T) :=
  biprod.mapIso (Iso.refl _) (biprod.mapIso (cochainTensorRotationIso P Q T).symm
    ((cochainTensorRotationIso P Q T) ≪≫ (cochainTensorRotationIso T P Q)).symm)

lemma cochainTensorCyclicSumStandardIso_rotation :
    cochainTensorCyclicSumRotation P Q T ≫ (cochainTensorCyclicSumStandardIso P Q T).hom =
      (cochainTensorCyclicSumStandardIso P Q T).hom ≫
        cochainCyclicThreeRotation (cochainTensor (cochainTensor P Q) T) := by
  have hr : (cochainTensorRotationIso Q T P).hom =
      ((cochainTensorRotationIso P Q T) ≪≫ (cochainTensorRotationIso T P Q)).inv := by
    apply (cancel_epi
      ((cochainTensorRotationIso P Q T) ≪≫ (cochainTensorRotationIso T P Q)).hom).mp
    rw [Iso.hom_inv_id]
    simpa only [Iso.trans_hom, Category.assoc] using cochainTensorRotation_cube P Q T
  apply biprod.hom_ext
  · simp [cochainTensorCyclicSumStandardIso, cochainTensorCyclicSumRotation,
      cochainCyclicThreeRotation, biprod.mapIso, Category.assoc, hr]
  · apply biprod.hom_ext
    · simp [cochainTensorCyclicSumStandardIso, cochainTensorCyclicSumRotation,
        cochainCyclicThreeRotation, biprod.mapIso, Category.assoc]
    · simp [cochainTensorCyclicSumStandardIso, cochainTensorCyclicSumRotation,
        cochainCyclicThreeRotation, biprod.mapIso, Category.assoc]

/-- Every Fourier eigenspace of a cyclic tensor orbit is the first tensor summand. -/
def cochainTensorCyclicSumEigenIso [Invertible (3 : R)] (a : R) (ha : a ^ 3 = 1) :
    ((cochainTensorCyclicSumAction P Q T).projector a ha).image ≅
      cochainTensor (cochainTensor P Q) T :=
  CochainIdempotent.imageIso ((cochainTensorCyclicSumAction P Q T).projector a ha)
    ((cochainCyclicThreeAction (cochainTensor (cochainTensor P Q) T)).projector a ha)
    (cochainTensorCyclicSumStandardIso P Q T)
    ((cochainTensorCyclicSumAction P Q T).projectorMap_naturality
      (cochainCyclicThreeAction (cochainTensor (cochainTensor P Q) T))
      (cochainTensorCyclicSumStandardIso P Q T).hom
      (cochainTensorCyclicSumStandardIso_rotation P Q T) a) ≪≫
    cochainCyclicThreeEigenIso (cochainTensor (cochainTensor P Q) T) a ha

end SerrePositivity
