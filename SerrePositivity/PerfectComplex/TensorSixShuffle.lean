module

public import SerrePositivity.PerfectComplex.TensorTriple

/-! # Six-factor tensor shuffles, grouping three pairs by their first and second factors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- Two four-factor shuffles separate the first and second entries of three pairs. -/
def cochainTensorSixShuffle (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (cochainTensor (cochainTensor P Q) (cochainTensor T U)) (cochainTensor V W) ≅
      cochainTensor (cochainTensor (cochainTensor P T) V) (cochainTensor (cochainTensor Q U) W) :=
  cochainTensorIso (cochainTensorShuffle P Q T U) (Iso.refl (cochainTensor V W)) ≪≫
    cochainTensorShuffle (cochainTensor P T) (cochainTensor Q U) V W

abbrev cochainTensorSixι (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l a b n : ℤ) (h : i + j + k + l + a + b = n) :=
  (cochainTensorQuadι P Q T U i j k l (i + j + k + l) rfl ⊗ₘ
    ιTensorObj V W a b (a + b) rfl) ≫
      ιTensorObj (cochainTensor (cochainTensor P Q) (cochainTensor T U)) (cochainTensor V W)
        (i + j + k + l) (a + b) n (by omega)

abbrev cochainTensorSixSeparatedι (P T V Q U W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i k a j l b n : ℤ) (h : i + k + a + j + l + b = n) :=
  (cochainTensorTripleι P T V i k a (i + k + a) rfl ⊗ₘ
    cochainTensorTripleι Q U W j l b (j + l + b) rfl) ≫
      ιTensorObj (cochainTensor (cochainTensor P T) V) (cochainTensor (cochainTensor Q U) W)
        (i + k + a) (j + l + b) n (by omega)

lemma cochainTensorSixShuffle_hom_apply_ι
    (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l a b n : ℤ) (h : i + j + k + l + a + b = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) (v : V.X a) (r : W.X b) :
    (cochainTensorSixShuffle P Q T U V W).hom.f n
      (cochainTensorSixι P Q T U V W i j k l a b n h
        (((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R] (v ⊗ₜ[R] r))) =
      (j * k + (j + l) * a).negOnePow •
        (cochainTensorSixSeparatedι P T V Q U W i k a j l b n (by omega)
          (((x ⊗ₜ[R] z) ⊗ₜ[R] v) ⊗ₜ[R] ((y ⊗ₜ[R] w) ⊗ₜ[R] r))) := by
  change (cochainTensorShuffle (cochainTensor P T) (cochainTensor Q U) V W).hom.f n
    ((cochainTensorMap (cochainTensorShuffle P Q T U).hom (𝟙 (cochainTensor V W))).f n
      (ιTensorObj (cochainTensor (cochainTensor P Q) (cochainTensor T U)) (cochainTensor V W)
        (i + j + k + l) (a + b) n (by omega)
        (cochainTensorQuadι P Q T U i j k l (i + j + k + l) rfl
          ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R]
            (ιTensorObj V W a b (a + b) rfl) (v ⊗ₜ[R] r)))) = _
  rw [cochainTensorMap_apply_ι, cochainTensorShuffle_hom_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, Units.smul_def,
    ← TensorProduct.smul_tmul', map_zsmul]
  rw [cochainTensorQuadι_apply]
  rw [cochainTensorQuad_apply_of_sum (cochainTensor P T) (cochainTensor Q U) V W
    (i + k) (j + l) a b (i + j + k + l) (a + b) n (by omega) rfl (by omega)]
  rw [cochainTensorShuffle_hom_apply_ι]
  simp only [Units.smul_def, smul_smul, Int.negOnePow_add, Units.val_mul]
  rw [cochainTensorQuadι_apply]
  rfl

/-- The shuffle signs agree after rotating all three pairs or the two separate triples. -/
lemma cochainTensorSixShuffle_rotation_sign (i j k l a b : ℤ) :
    ((i + j + k + l) * (a + b)).negOnePow * (b * i + (b + j) * k).negOnePow =
      (j * k + (j + l) * a).negOnePow * ((i + k) * a + (j + l) * b).negOnePow := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  have h : (i + j + k + l) * (a + b) + (b * i + (b + j) * k) =
      (j * k + (j + l) * a + ((i + k) * a + (j + l) * b)) + 2 * (b * (i + k)) := by ring
  rw [h, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

end SerrePositivity
