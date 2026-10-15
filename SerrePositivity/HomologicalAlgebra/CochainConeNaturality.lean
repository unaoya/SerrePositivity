module

public import SerrePositivity.HomologicalAlgebra.CochainConeCoordinates
public import SerrePositivity.HomologicalAlgebra.CochainConeArrowMap

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
  have h : i + 1 = j := hij
  subst j
  exact cochainConeArrowMap_inl φ ψ α i

/-- 可換正方形からの錐の写像は、第2包含について右側の写像を誘導する。 -/
@[reassoc] theorem moduleConeArrowMap_inr (i : ℤ) :
    inrX φ i ≫ (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i =
      α.right.f i ≫ inrX ψ i := by
  exact cochainConeArrowMap_inr φ ψ α i

/-- 錐の写像の第1射影は、左側の写像の第1成分。 -/
@[reassoc] theorem moduleConeArrowMap_fst (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i ≫ fstX ψ i j hij =
      fstX φ i j hij ≫ α.left.f j := by
  have h : i + 1 = j := hij
  subst j
  exact cochainConeArrowMap_fst φ ψ α i

/-- 錐の写像の第2射影は、右側の写像の第2成分。 -/
@[reassoc] theorem moduleConeArrowMap_snd (i : ℤ) :
    (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i ≫ sndX ψ i =
      sndX φ i ≫ α.right.f i := by
  exact cochainConeArrowMap_snd φ ψ α i

end SerrePositivity.DerivedCompletion
