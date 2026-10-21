module

public import SerrePositivity.KST.LocalizingInvariants.CochainTensorShiftElements

/-!
概要：第一因子の shift と三重 tensor の associator の整合性。
方針：符号を持たない左因子 shift を斉次三重 tensor 上で比較する。
規約：元の全 chain map の等式。使われ方：shift した右作用の結合則。
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
lemma tensorShift_associator_left (P Q T : CochainComplex (ModuleCat R) ℤ) (s : ℤ) :
    (cochainTensorAssociator (P⟦s⟧) Q T).hom ≫
      (cochainTensorShiftLeft P (cochainTensor Q T) s).hom =
    ((cochainTensorShiftLeft P Q s).hom ▷ T) ≫
      (cochainTensorShiftLeft (cochainTensor P Q) T s).hom ≫
        (cochainTensorAssociator P Q T).hom⟦s⟧' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext (P⟦s⟧) Q T n
  intro i j k h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorShiftLeft P (cochainTensor Q T) s).hom.f n
    ((cochainTensorAssociator (P⟦s⟧) Q T).hom.f n
      (cochainTensorTripleι (P⟦s⟧) Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))) =
    (cochainTensorAssociator P Q T).hom.f (n + s)
      ((cochainTensorShiftLeft (cochainTensor P Q) T s).hom.f n
        ((cochainTensorMap (cochainTensorShiftLeft P Q s).hom (𝟙 T)).f n
          (cochainTensorTripleι (P⟦s⟧) Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))))
  rw [cochainTensorTripleι_apply, cochainTensorAssociator_hom_apply_ι,
    tensorShiftLeft_apply, cochainTensorMap_apply_ι, tensorShiftLeft_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [tensorShiftLeft_apply, cochainTensorAssociator_hom_apply_ι_of_sum]

end SerrePositivity.KST.LocalizingInvariants
