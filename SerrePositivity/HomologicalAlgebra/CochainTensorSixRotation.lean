module

public import SerrePositivity.HomologicalAlgebra.CochainTensorSixHomogeneous

/-! # Homogeneous formulas for source and target rotations of six tensor factors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

lemma cochainTensorRotation_apply_ι_of_sum
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k s n : ℤ)
    (hs : i + j = s) (h : s + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensorRotationIso P Q T).hom.f n
      (ιTensorObj (cochainTensor P Q) T s k n h
        ((ιTensorObj P Q i j s hs) (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      (s * k).negOnePow •
        (cochainTensorTripleι T P Q k i j n (by omega) ((z ⊗ₜ[R] x) ⊗ₜ[R] y)) := by
  subst hs
  exact cochainTensorRotation_apply_ι P Q T i j k n h x y z

lemma cochainTensorSix_apply_of_sum
    (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l a b s r n : ℤ) (hs : i + j + k + l = s) (hr : a + b = r) (h : s + r = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) (v : V.X a) (e : W.X b) :
    ιTensorObj (cochainTensor (cochainTensor P Q) (cochainTensor T U)) (cochainTensor V W)
      s r n h (cochainTensorQuadι P Q T U i j k l s hs
        ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R]
          (ιTensorObj V W a b r hr) (v ⊗ₜ[R] e)) =
      cochainTensorSixι P Q T U V W i j k l a b n (by omega)
        (((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R] (v ⊗ₜ[R] e)) := by
  subst hs
  subst hr
  rfl

lemma cochainTensorSixSeparated_apply_of_sum
    (P T V Q U W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i k a j l b s r n : ℤ) (hs : i + k + a = s) (hr : j + l + b = r) (h : s + r = n)
    (x : P.X i) (z : T.X k) (v : V.X a) (y : Q.X j) (w : U.X l) (e : W.X b) :
    ιTensorObj (cochainTensor (cochainTensor P T) V) (cochainTensor (cochainTensor Q U) W)
      s r n h (cochainTensorTripleι P T V i k a s hs ((x ⊗ₜ[R] z) ⊗ₜ[R] v) ⊗ₜ[R]
        cochainTensorTripleι Q U W j l b r hr ((y ⊗ₜ[R] w) ⊗ₜ[R] e)) =
      cochainTensorSixSeparatedι P T V Q U W i k a j l b n (by omega)
        (((x ⊗ₜ[R] z) ⊗ₜ[R] v) ⊗ₜ[R] ((y ⊗ₜ[R] w) ⊗ₜ[R] e)) := by
  subst hs
  subst hr
  rfl

lemma cochainTensorSix_sourceRotation_apply_ι
    (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l a b n : ℤ) (h : i + j + k + l + a + b = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) (v : V.X a) (e : W.X b) :
    (cochainTensorRotationIso (cochainTensor P Q) (cochainTensor T U)
      (cochainTensor V W)).hom.f n
      (cochainTensorSixι P Q T U V W i j k l a b n h
        (((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R] (v ⊗ₜ[R] e))) =
      ((i + j + k + l) * (a + b)).negOnePow •
        (cochainTensorSixι V W P Q T U a b i j k l n (by omega)
          (((v ⊗ₜ[R] e) ⊗ₜ[R] (x ⊗ₜ[R] y)) ⊗ₜ[R] (z ⊗ₜ[R] w))) := by
  change (cochainTensorRotationIso (cochainTensor P Q) (cochainTensor T U)
    (cochainTensor V W)).hom.f n
    (ιTensorObj (cochainTensor (cochainTensor P Q) (cochainTensor T U)) (cochainTensor V W)
      (i + j + k + l) (a + b) n (by omega)
      (cochainTensorQuadι P Q T U i j k l (i + j + k + l) rfl
        ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R]
          (ιTensorObj V W a b (a + b) rfl) (v ⊗ₜ[R] e))) = _
  rw [cochainTensorQuadι_apply, cochainTensorRotation_apply_ι_of_sum]
  rw [cochainTensorTripleι_apply]
  rw [cochainTensorQuad_apply_of_sum V W P Q a b i j (a + b) (i + j)
    (a + b + (i + j)) rfl rfl rfl]
  rw [cochainTensorSix_apply_of_sum]

lemma cochainTensorSix_diagonalRotation_apply_ι
    (P T V Q U W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i k a j l b n : ℤ) (h : i + k + a + j + l + b = n)
    (x : P.X i) (z : T.X k) (v : V.X a) (y : Q.X j) (w : U.X l) (e : W.X b) :
    (cochainTensorMap (cochainTensorRotationIso P T V).hom
      (cochainTensorRotationIso Q U W).hom).f n
      (cochainTensorSixSeparatedι P T V Q U W i k a j l b n h
        (((x ⊗ₜ[R] z) ⊗ₜ[R] v) ⊗ₜ[R] ((y ⊗ₜ[R] w) ⊗ₜ[R] e))) =
      ((i + k) * a + (j + l) * b).negOnePow •
        (cochainTensorSixSeparatedι V P T W Q U a i k b j l n (by omega)
          (((v ⊗ₜ[R] x) ⊗ₜ[R] z) ⊗ₜ[R] ((e ⊗ₜ[R] y) ⊗ₜ[R] w))) := by
  change (cochainTensorMap (cochainTensorRotationIso P T V).hom
    (cochainTensorRotationIso Q U W).hom).f n
    (ιTensorObj (cochainTensor (cochainTensor P T) V) (cochainTensor (cochainTensor Q U) W)
      (i + k + a) (j + l + b) n (by omega)
      (cochainTensorTripleι P T V i k a (i + k + a) rfl ((x ⊗ₜ[R] z) ⊗ₜ[R] v) ⊗ₜ[R]
        cochainTensorTripleι Q U W j l b (j + l + b) rfl ((y ⊗ₜ[R] w) ⊗ₜ[R] e))) = _
  rw [cochainTensorMap_apply_ι, cochainTensorRotation_apply_ι, cochainTensorRotation_apply_ι]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    map_zsmul, smul_smul, Int.negOnePow_add, Units.val_mul]
  rw [cochainTensorSixSeparated_apply_of_sum]
  rw [mul_comm (((j + l) * b).negOnePow : ℤ) (((i + k) * a).negOnePow : ℤ)]

end SerrePositivity
