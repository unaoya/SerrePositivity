module

public import SerrePositivity.PerfectComplex.TensorSixRotation

/-! # Six-factor tensor shuffles intertwine cyclic and diagonal rotations -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

@[reassoc]
lemma cochainTensorSixShuffle_rotation
    (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorRotationIso (cochainTensor P Q) (cochainTensor T U) (cochainTensor V W)).hom ≫
      (cochainTensorSixShuffle V W P Q T U).hom =
    (cochainTensorSixShuffle P Q T U V W).hom ≫
      cochainTensorMap (cochainTensorRotationIso P T V).hom
        (cochainTensorRotationIso Q U W).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorSix_hom_ext P Q T U V W n
  intro i j k l a b h
  apply ModuleCat.hom_ext
  apply tensorProductSix_ext_pairs
  intro x y z w v e
  change (cochainTensorSixShuffle V W P Q T U).hom.f n
    ((cochainTensorRotationIso (cochainTensor P Q) (cochainTensor T U)
      (cochainTensor V W)).hom.f n
      (cochainTensorSixι P Q T U V W i j k l a b n h
        (((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R] (v ⊗ₜ[R] e)))) =
    (cochainTensorMap (cochainTensorRotationIso P T V).hom
      (cochainTensorRotationIso Q U W).hom).f n
      ((cochainTensorSixShuffle P Q T U V W).hom.f n
        (cochainTensorSixι P Q T U V W i j k l a b n h
          (((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R] (v ⊗ₜ[R] e))))
  rw [cochainTensorSix_sourceRotation_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorSixShuffle_hom_apply_ι, cochainTensorSixShuffle_hom_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorSix_diagonalRotation_apply_ι]
  simpa only [Units.smul_def, smul_smul, Units.val_mul] using
    congrArg (fun r : ℤˣ => r •
      (cochainTensorSixSeparatedι V P T W Q U a i k b j l n (by omega)
        (((v ⊗ₜ[R] x) ⊗ₜ[R] z) ⊗ₜ[R] ((e ⊗ₜ[R] y) ⊗ₜ[R] w))))
      (cochainTensorSixShuffle_rotation_sign i j k l a b)

end SerrePositivity
