module

public import SerrePositivity.KST.LocalizingInvariants.CochainTensorShiftElements
public import SerrePositivity.HomologicalAlgebra.CochainTensorHexagon

/-!
概要：第三因子の shift と三重 tensor の associator の整合性を証明する。
方針：斉次三重 tensor 上で二つの Koszul 符号を加法公式で比較する。
規約：元の全 chain map の等式。使われ方：shift した左作用の結合則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R]

@[reassoc]
lemma tensorShift_associator_right (P Q T : CochainComplex (ModuleCat R) ℤ) (s : ℤ) :
    (cochainTensorAssociator P Q (T⟦s⟧)).hom ≫
      (P ◁ (cochainTensorShiftRight Q T s).hom) ≫
        (cochainTensorShiftRight P (cochainTensor Q T) s).hom =
    (cochainTensorShiftRight (cochainTensor P Q) T s).hom ≫
      (cochainTensorAssociator P Q T).hom⟦s⟧' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext P Q (T⟦s⟧) n
  intro i j k h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorShiftRight P (cochainTensor Q T) s).hom.f n
    ((cochainTensorMap (𝟙 P) (cochainTensorShiftRight Q T s).hom).f n
      ((cochainTensorAssociator P Q (T⟦s⟧)).hom.f n
        (cochainTensorTripleι P Q (T⟦s⟧) i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))) =
    (cochainTensorAssociator P Q T).hom.f (n + s)
      ((cochainTensorShiftRight (cochainTensor P Q) T s).hom.f n
        (cochainTensorTripleι P Q (T⟦s⟧) i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))
  rw [cochainTensorTripleι_apply, cochainTensorAssociator_hom_apply_ι,
    cochainTensorMap_apply_ι, tensorShiftRight_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, Units.smul_def,
    TensorProduct.tmul_smul, map_zsmul]
  rw [tensorShiftRight_apply, tensorShiftRight_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorAssociator_hom_apply_ι_of_sum]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul, smul_smul]
  rw [cochainTensorRightTriple_apply_of_sum P Q T i j (k + s) (j + k + s) (n + s)
    (by omega) (by omega) x y z]
  simp only [add_mul, Int.negOnePow_add, Units.val_mul]

end SerrePositivity.KST.LocalizingInvariants
