module

public import SerrePositivity.KST.LocalizingInvariants.CochainTensorShiftAssociatorRight

/-!
概要：第二因子の shift と三重 tensor の associator の整合性。
方針：左右 tensor–shift の斉次元表示と中間次数の正規化で比較する。
規約：Koszul 符号を保持。使われ方：shift 後の左右作用の交換則。
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
lemma tensorShift_associator_middle (P Q T : CochainComplex (ModuleCat R) ℤ) (s : ℤ) :
    (cochainTensorAssociator P (Q⟦s⟧) T).hom ≫
      (P ◁ (cochainTensorShiftLeft Q T s).hom) ≫
        (cochainTensorShiftRight P (cochainTensor Q T) s).hom =
    ((cochainTensorShiftRight P Q s).hom ▷ T) ≫
      (cochainTensorShiftLeft (cochainTensor P Q) T s).hom ≫
        (cochainTensorAssociator P Q T).hom⟦s⟧' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext P (Q⟦s⟧) T n
  intro i j k h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorShiftRight P (cochainTensor Q T) s).hom.f n
    ((cochainTensorMap (𝟙 P) (cochainTensorShiftLeft Q T s).hom).f n
      ((cochainTensorAssociator P (Q⟦s⟧) T).hom.f n
        (cochainTensorTripleι P (Q⟦s⟧) T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))) =
    (cochainTensorAssociator P Q T).hom.f (n + s)
      ((cochainTensorShiftLeft (cochainTensor P Q) T s).hom.f n
        ((cochainTensorMap (cochainTensorShiftRight P Q s).hom (𝟙 T)).f n
          (cochainTensorTripleι P (Q⟦s⟧) T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))))
  rw [cochainTensorTripleι_apply, cochainTensorAssociator_hom_apply_ι,
    cochainTensorMap_apply_ι, tensorShiftLeft_apply, tensorShiftRight_apply,
    cochainTensorMap_apply_ι, tensorShiftRight_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, Units.smul_def,
    ← TensorProduct.smul_tmul', map_zsmul]
  rw [tensorShiftLeft_apply, cochainTensorAssociator_hom_apply_ι_of_sum]
  rw [cochainTensorRightTriple_apply_of_sum P Q T i (j + s) k (j + k + s) (n + s)
    (by omega) (by omega) x y z]

end SerrePositivity.KST.LocalizingInvariants
