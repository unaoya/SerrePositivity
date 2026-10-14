module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleConeCoordinates

/-! # 加群のmapping coneの成分表示の自然性

可換正方形から誘導される錐の写像を、包含と射影で計算する。
-/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category
open HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]
variable {P Q P' Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : P ⟶ Q) (ψ : P' ⟶ Q') (α : Arrow.mk φ ⟶ Arrow.mk ψ)

/-- 可換正方形からの錐の写像は、第1包含について左側の写像を誘導する。 -/
@[reassoc] theorem moduleConeArrowMap_inl (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    inlX φ j i hij ≫ (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i =
      α.left.f j ≫ inlX ψ j i hij := by
  rw [mapArrowHom, inlX_desc_f _ _ _ _ _ hij]
  simp only [HomologicalComplex.homotopyCofiber_X, Arrow.mk_right, Arrow.mk_left,
    Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.compLeft_hom,
    add_zero, zero_add]
  rw [inrCompHomotopy_hom ψ (fun k ↦ ⟨k - 1, by simp⟩) j i hij]

/-- 可換正方形からの錐の写像は、第2包含について右側の写像を誘導する。 -/
@[reassoc] theorem moduleConeArrowMap_inr (i : ℤ) :
    inrX φ i ≫ (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i =
      α.right.f i ≫ inrX ψ i := by
  rw [mapArrowHom, inrX_desc_f]
  rfl

/-- 錐の写像の第1射影は、左側の写像の第1成分。 -/
@[reassoc] theorem moduleConeArrowMap_fst (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i ≫ fstX ψ i j hij =
      fstX φ i j hij ≫ α.left.f j := by
  apply ext_from_X φ j i hij
  · simp only [moduleConeArrowMap_inl_assoc, inlX_fstX,
      inlX_fstX_assoc]
    rfl
  · simp only [moduleConeArrowMap_inr_assoc, inrX_fstX,
      inrX_fstX_assoc, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

/-- 錐の写像の第2射影は、右側の写像の第2成分。 -/
@[reassoc] theorem moduleConeArrowMap_snd (i : ℤ) :
    (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i ≫ sndX ψ i =
      sndX φ i ≫ α.right.f i := by
  apply ext_from_X φ (i + 1) i rfl
  · simp only [moduleConeArrowMap_inl_assoc, inlX_sndX,
      inlX_sndX_assoc, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  · simp only [moduleConeArrowMap_inr_assoc, inrX_sndX,
      inrX_sndX_assoc]
    rfl

end SerrePositivity.DerivedCompletion
