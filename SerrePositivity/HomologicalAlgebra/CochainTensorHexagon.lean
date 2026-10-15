module
public import SerrePositivity.HomologicalAlgebra.CochainTensorTriple

/-! # Hexagon compatibility for the actual signed cochain symmetry -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- Normalize the intermediate total degree in a right-associated tensor inclusion. -/
lemma cochainTensorRightTriple_apply_of_sum
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k s n : ℤ)
    (hs : j + k = s) (h : i + s = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    ιTensorObj P (cochainTensor Q T) i s n h
        (x ⊗ₜ[R] ιTensorObj Q T j k s hs (y ⊗ₜ[R] z)) =
      ιTensorObj P (cochainTensor Q T) i (j + k) n (by omega)
        (x ⊗ₜ[R] ιTensorObj Q T j k (j + k) rfl (y ⊗ₜ[R] z)) := by
  subst s
  rfl

/-- The signed tensor symmetry and the standard associator satisfy the first hexagon. -/
lemma cochainTensorSymmetry_hexagon_forward
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorAssociator P Q T).hom ≫
        (cochainTensorSymmetry P (cochainTensor Q T)).hom ≫
        (cochainTensorAssociator Q T P).hom =
      cochainTensorMap (cochainTensorSymmetry P Q).hom (𝟙 T) ≫
        (cochainTensorAssociator Q P T).hom ≫
        cochainTensorMap (𝟙 Q) (cochainTensorSymmetry P T).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext P Q T n
  intro i j k h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorAssociator Q T P).hom.f n
      ((cochainTensorSymmetry P (cochainTensor Q T)).hom.f n
        ((cochainTensorAssociator P Q T).hom.f n
          (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))) =
    (cochainTensorMap (𝟙 Q) (cochainTensorSymmetry P T).hom).f n
      ((cochainTensorAssociator Q P T).hom.f n
        ((cochainTensorMap (cochainTensorSymmetry P Q).hom (𝟙 T)).f n
          (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))))
  rw [cochainTensorTripleι_apply, cochainTensorAssociator_hom_apply_ι,
    cochainTensorSymmetry_hom_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorAssociator_hom_apply_ι_of_sum]
  rw [cochainTensorMap_apply_ι, cochainTensorSymmetry_hom_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, Units.smul_def,
    ← TensorProduct.smul_tmul', map_zsmul]
  rw [cochainTensorAssociator_hom_apply_ι_of_sum, cochainTensorMap_apply_ι,
    cochainTensorSymmetry_hom_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, Units.smul_def,
    TensorProduct.tmul_smul, map_zsmul, smul_smul]
  simp only [mul_add, Int.negOnePow_add, Units.val_mul]
  rw [cochainTensorRightTriple_apply_of_sum Q T P j k i (i + k) n
    (add_comm k i) (by omega) y z x]

/-- The inverse signed symmetry is the symmetry in the reverse order. -/
@[simp]
lemma cochainTensorSymmetry_inv (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorSymmetry P Q).inv = (cochainTensorSymmetry Q P).hom := by
  apply (cancel_epi (cochainTensorSymmetry P Q).hom).mp
  rw [Iso.hom_inv_id, cochainTensorSymmetry_hom_comp]

end SerrePositivity
