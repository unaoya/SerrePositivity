module
public import SerrePositivity.HomologicalAlgebra.CochainConeNaturality
public import Mathlib.Algebra.Homology.Additive

/-! # Naturality of additive change of coefficients for cochain mapping cones -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HomologicalComplex.homotopyCofiber DerivedCompletion
variable {R S : Type u} [CommRing R] [CommRing S]
variable (H : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [H.Additive]
variable {K L K' L' : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : K ⟶ L) (ψ : K' ⟶ L') (α : Arrow.mk φ ⟶ Arrow.mk ψ)

/-- The actual additive cone comparison is natural for all commutative squares. -/
@[reassoc]
lemma cochainConeAdditiveIso_inv_naturality :
    (mapHomologicalComplexObjIso φ H).inv ≫
        (H.mapHomologicalComplex (.up ℤ)).map
          (mapArrowHom φ ψ (fun j => ⟨j - 1, by simp⟩) α) =
      mapArrowHom ((H.mapHomologicalComplex (.up ℤ)).map φ)
        ((H.mapHomologicalComplex (.up ℤ)).map ψ) (fun j => ⟨j - 1, by simp⟩)
        ((H.mapHomologicalComplex (.up ℤ)).mapArrow.map α) ≫
          (mapHomologicalComplexObjIso ψ H).inv := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ext_from_X ((H.mapHomologicalComplex (.up ℤ)).map φ) (q + 1) q rfl
  · change (inlX _ (q + 1) q rfl ≫ (mapHomologicalComplexObjXIso φ H q).inv) ≫
        H.map ((mapArrowHom φ ψ (fun j => ⟨j - 1, by simp⟩) α).f q) = _
    rw [inlX_mapHomologicalComplexObjXIso_inv, ← H.map_comp, moduleConeArrowMap_inl]
    simp only [HomologicalComplex.comp_f, moduleConeArrowMap_inl_assoc, H.map_comp]
    change _ = H.map (α.left.f (q + 1)) ≫
      inlX ((H.mapHomologicalComplex (.up ℤ)).map ψ) (q + 1) q rfl ≫
      (mapHomologicalComplexObjXIso ψ H q).inv
    rw [inlX_mapHomologicalComplexObjXIso_inv]
  · change (inrX _ q ≫ (mapHomologicalComplexObjXIso φ H q).inv) ≫
        H.map ((mapArrowHom φ ψ (fun j => ⟨j - 1, by simp⟩) α).f q) = _
    rw [inrX_mapHomologicalComplexObjXIso_inv, ← H.map_comp, moduleConeArrowMap_inr]
    simp only [HomologicalComplex.comp_f, moduleConeArrowMap_inr_assoc, H.map_comp]
    change _ = H.map (α.right.f q) ≫ inrX ((H.mapHomologicalComplex (.up ℤ)).map ψ) q ≫
      (mapHomologicalComplexObjXIso ψ H q).inv
    rw [inrX_mapHomologicalComplexObjXIso_inv]

/-- The forward cone comparison commutes with the actual induced cone maps. -/
@[reassoc]
lemma cochainConeAdditiveIso_hom_naturality :
    (H.mapHomologicalComplex (.up ℤ)).map
        (mapArrowHom φ ψ (fun j => ⟨j - 1, by simp⟩) α) ≫
          (mapHomologicalComplexObjIso ψ H).hom =
      (mapHomologicalComplexObjIso φ H).hom ≫
        mapArrowHom ((H.mapHomologicalComplex (.up ℤ)).map φ)
          ((H.mapHomologicalComplex (.up ℤ)).map ψ) (fun j => ⟨j - 1, by simp⟩)
          ((H.mapHomologicalComplex (.up ℤ)).mapArrow.map α) := by
  have h := congrArg
    (fun f => (mapHomologicalComplexObjIso φ H).hom ≫ f ≫
      (mapHomologicalComplexObjIso ψ H).hom)
    (cochainConeAdditiveIso_inv_naturality H φ ψ α)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

end SerrePositivity
