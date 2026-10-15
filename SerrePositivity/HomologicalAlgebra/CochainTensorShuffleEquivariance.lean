module

public import SerrePositivity.HomologicalAlgebra.CochainTensorHomogeneous

/-! # Four-factor tensor shuffles intertwine block exchange and diagonal exchange -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

lemma cochainTensorQuad_diagonalSymmetry_apply_ι
    (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l n : ℤ) (h : i + j + k + l = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    (cochainTensorMap (cochainTensorSymmetry P Q).hom (cochainTensorSymmetry T U).hom).f n
      (cochainTensorQuadι P Q T U i j k l n h ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w))) =
    (i * j + k * l).negOnePow •
      (cochainTensorQuadι Q P U T j i l k n (by omega) ((y ⊗ₜ[R] x) ⊗ₜ[R] (w ⊗ₜ[R] z))) := by
  rw [cochainTensorQuadι_apply, cochainTensorMap_apply_ι,
    cochainTensorSymmetry_hom_apply_ι, cochainTensorSymmetry_hom_apply_ι]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    map_zsmul, smul_smul, Int.negOnePow_add, Units.val_mul]
  rw [cochainTensorQuad_apply_of_sum]
  rw [mul_comm ((k * l).negOnePow : ℤ) ((i * j).negOnePow : ℤ)]

lemma cochainTensorShuffle_exchange_sign (i j k l : ℤ) :
    ((i + j) * (k + l)).negOnePow * (l * i).negOnePow =
      (j * k).negOnePow * (i * k + j * l).negOnePow := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  have he : (i + j) * (k + l) + l * i = (j * k + (i * k + j * l)) + 2 * (i * l) := by
    ring
  rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

lemma cochainTensorShuffle_symmetry
    (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorSymmetry (cochainTensor P Q) (cochainTensor T U)).hom ≫
      (cochainTensorShuffle T U P Q).hom =
    (cochainTensorShuffle P Q T U).hom ≫
      cochainTensorMap (cochainTensorSymmetry P T).hom (cochainTensorSymmetry Q U).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorQuad_hom_ext P Q T U n
  intro i j k l h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_fourfold'
  intro x y z w
  change (cochainTensorShuffle T U P Q).hom.f n
      ((cochainTensorSymmetry (cochainTensor P Q) (cochainTensor T U)).hom.f n
        (cochainTensorQuadι P Q T U i j k l n h ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)))) =
    (cochainTensorMap (cochainTensorSymmetry P T).hom (cochainTensorSymmetry Q U).hom).f n
      ((cochainTensorShuffle P Q T U).hom.f n
        (cochainTensorQuadι P Q T U i j k l n h ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w))))
  rw [cochainTensorQuad_symmetry_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorShuffle_hom_apply_ι, cochainTensorShuffle_hom_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorQuad_diagonalSymmetry_apply_ι]
  simpa only [Units.smul_def, smul_smul, Units.val_mul] using
    congrArg (fun r : ℤˣ => r •
      (cochainTensorQuadι T P U Q k i l j n (by omega)
        ((z ⊗ₜ[R] x) ⊗ₜ[R] (w ⊗ₜ[R] y))))
      (cochainTensorShuffle_exchange_sign i j k l)

end SerrePositivity
