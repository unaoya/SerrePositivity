module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Components of the functorial mapping-cone map -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {P Q P' Q' : CochainComplex C ℤ} (f : P ⟶ Q) (g : P' ⟶ Q')
  [HasHomotopyCofiber f] [HasHomotopyCofiber g]
  (α : Arrow.mk f ⟶ Arrow.mk g)

abbrev cochainConeArrowMap : mappingCone f ⟶ mappingCone g :=
  homotopyCofiber.mapArrowHom f g (fun j => ⟨j - 1, by simp⟩) α

@[reassoc (attr := simp)]
lemma cochainConeArrowMap_inr (n : ℤ) :
    (mappingCone.inr f).f n ≫ (cochainConeArrowMap f g α).f n =
      α.right.f n ≫ (mappingCone.inr g).f n := by
  simp [cochainConeArrowMap, homotopyCofiber.mapArrowHom, mappingCone.inr]

@[reassoc (attr := simp)]
lemma cochainConeArrowMap_inl (n : ℤ) :
    (mappingCone.inl f).v (n + 1) n (by omega) ≫ (cochainConeArrowMap f g α).f n =
      α.left.f (n + 1) ≫ (mappingCone.inl g).v (n + 1) n (by omega) := by
  simp [cochainConeArrowMap, homotopyCofiber.mapArrowHom, mappingCone.inl,
    homotopyCofiber.inrCompHomotopy_hom]

@[reassoc (attr := simp)]
lemma cochainConeArrowMap_fst (n : ℤ) :
    (cochainConeArrowMap f g α).f n ≫ (mappingCone.fst g).1.v n (n + 1) rfl =
      (mappingCone.fst f).1.v n (n + 1) rfl ≫ α.left.f (n + 1) := by
  apply mappingCone.ext_from f (n + 1) n (by omega)
  · simp [cochainConeArrowMap_inl_assoc]
  · simp [cochainConeArrowMap_inr_assoc]

@[reassoc (attr := simp)]
lemma cochainConeArrowMap_snd (n : ℤ) :
    (cochainConeArrowMap f g α).f n ≫ (mappingCone.snd g).v n n (by omega) =
      (mappingCone.snd f).v n n (by omega) ≫ α.right.f n := by
  apply mappingCone.ext_from f (n + 1) n (by omega)
  · simp [cochainConeArrowMap_inl_assoc]
  · simp [cochainConeArrowMap_inr_assoc]

end SerrePositivity
