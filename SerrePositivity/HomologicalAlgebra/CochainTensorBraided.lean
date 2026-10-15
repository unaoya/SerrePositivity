module
public import SerrePositivity.HomologicalAlgebra.CochainTensorHexagon

/-! # The symmetric monoidal structure given by the actual signed cochain symmetry -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
variable {R : Type u} [CommRing R]

/-- Involutivity and the first hexagon give the second hexagon, with the actual maps. -/
lemma cochainTensorSymmetry_hexagon_reverse
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorAssociator P Q T).inv ≫
        (cochainTensorSymmetry (cochainTensor P Q) T).hom ≫
        (cochainTensorAssociator T P Q).inv =
      cochainTensorMap (𝟙 P) (cochainTensorSymmetry Q T).hom ≫
        (cochainTensorAssociator P T Q).inv ≫
        cochainTensorMap (cochainTensorSymmetry P T).hom (𝟙 Q) := by
  have h :
      cochainTensorAssociator T P Q ≪≫ cochainTensorSymmetry T (cochainTensor P Q) ≪≫
          cochainTensorAssociator P Q T =
        cochainTensorIso (cochainTensorSymmetry T P) (Iso.refl Q) ≪≫
          cochainTensorAssociator P T Q ≪≫
          cochainTensorIso (Iso.refl P) (cochainTensorSymmetry T Q) := by
    apply Iso.ext
    exact cochainTensorSymmetry_hexagon_forward T P Q
  have hi := congrArg Iso.inv h
  simp only [Iso.trans_inv, cochainTensorIso, MonoidalCategory.tensorIso_inv,
    Iso.refl_inv, cochainTensorSymmetry_inv, Category.assoc] at hi
  exact hi

/-- The existing cochain tensor is symmetric monoidal with its actual Koszul-signed symmetry. -/
instance cochainTensorSymmetricCategory :
    SymmetricCategory (CochainComplex (ModuleCat.{u} R) ℤ) where
  braiding := cochainTensorSymmetry
  braiding_naturality_right := by
    intro P Q T f
    exact cochainTensorSymmetry_naturality (𝟙 P) f
  braiding_naturality_left := by
    intro P Q f T
    exact cochainTensorSymmetry_naturality f (𝟙 T)
  hexagon_forward := cochainTensorSymmetry_hexagon_forward
  hexagon_reverse := cochainTensorSymmetry_hexagon_reverse
  symmetry := cochainTensorSymmetry_hom_comp

end SerrePositivity
