module

public import SerrePositivity.PerfectComplex.TensorHomotopy

/-! # Four-factor tensor shuffles for integer cochain complexes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

@[reassoc]
lemma ιTensorObj_cochainTensorAssociator_hom
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k n : ℤ) (h : i + j + k = n) :
    (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
      ιTensorObj (cochainTensor P Q) T (i + j) k n h ≫
      (cochainTensorAssociator P Q T).hom.f n =
    (α_ (P.X i) (Q.X j) (T.X k)).hom ≫
      (P.X i ◁ ιTensorObj Q T j k (j + k) rfl) ≫
      ιTensorObj P (cochainTensor Q T) i (j + k) n (by omega) :=
  GradedObject.Monoidal.ιTensorObj₃'_associator_hom P.X Q.X T.X i j k n h

@[reassoc]
lemma ιTensorObj_cochainTensorAssociator_inv
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k n : ℤ) (h : i + j + k = n) :
    (P.X i ◁ ιTensorObj Q T j k (j + k) rfl) ≫
      ιTensorObj P (cochainTensor Q T) i (j + k) n (by omega) ≫
      (cochainTensorAssociator P Q T).inv.f n =
    (α_ (P.X i) (Q.X j) (T.X k)).inv ≫
      (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
      ιTensorObj (cochainTensor P Q) T (i + j) k n h :=
  GradedObject.Monoidal.ιTensorObj₃_associator_inv P.X Q.X T.X i j k n h

def cochainTensorIso {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : P ≅ P') (f : Q ≅ Q') : cochainTensor P Q ≅ cochainTensor P' Q' where
  hom := cochainTensorMap e.hom f.hom
  inv := cochainTensorMap e.inv f.inv
  hom_inv_id := by
    rw [cochainTensorMap_comp, e.hom_inv_id, f.hom_inv_id, cochainTensorMap_id]
  inv_hom_id := by
    rw [cochainTensorMap_comp, e.inv_hom_id, f.inv_hom_id, cochainTensorMap_id]

/-- Move the two middle factors past each other, with the existing Koszul-signed symmetry. -/
def cochainTensorShuffle (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (cochainTensor P Q) (cochainTensor T U) ≅
      cochainTensor (cochainTensor P T) (cochainTensor Q U) :=
  cochainTensorAssociator P Q (cochainTensor T U) ≪≫
    cochainTensorIso (Iso.refl P) (cochainTensorAssociator Q T U).symm ≪≫
    cochainTensorIso (Iso.refl P)
      (cochainTensorIso (cochainTensorSymmetry Q T) (Iso.refl U)) ≪≫
    cochainTensorIso (Iso.refl P) (cochainTensorAssociator T Q U) ≪≫
    (cochainTensorAssociator P T (cochainTensor Q U)).symm

end SerrePositivity
