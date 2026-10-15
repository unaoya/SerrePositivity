module

public import SerrePositivity.HomologicalAlgebra.CochainConeCoordinates

/-! # Product coordinates and differential formulas for module mapping cones -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- Product coordinates of an ordinary cone term. -/
def mappingConeTermProdIso (q : ℤ) :
    (CochainComplex.mappingCone φ).X q ≅ ModuleCat.of R (K.X (q + 1) × L.X q) :=
  XIsoBiprod φ q (q + 1) rfl ≪≫ ModuleCat.biprodIsoProd _ _

/-- The first product projection is the actual cone projection. -/
lemma mappingConeTermProdIso_fst (q : ℤ) :
    (mappingConeTermProdIso φ q).hom ≫
        ModuleCat.ofHom (LinearMap.fst R (K.X (q + 1)) (L.X q)) =
      fstX φ q (q + 1) rfl := by
  have hb : (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).hom ≫
      ModuleCat.ofHom (LinearMap.fst R (K.X (q + 1)) (L.X q)) = biprod.fst := by
    apply (cancel_epi (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ModuleCat.biprodIsoProd_inv_comp_fst]
  dsimp only [mappingConeTermProdIso, Iso.trans_hom]
  rw [Category.assoc, hb]
  rfl

/-- The second product projection is the actual cone projection. -/
lemma mappingConeTermProdIso_snd (q : ℤ) :
    (mappingConeTermProdIso φ q).hom ≫
        ModuleCat.ofHom (LinearMap.snd R (K.X (q + 1)) (L.X q)) = sndX φ q := by
  have hb : (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).hom ≫
      ModuleCat.ofHom (LinearMap.snd R (K.X (q + 1)) (L.X q)) = biprod.snd := by
    apply (cancel_epi (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ModuleCat.biprodIsoProd_inv_comp_snd]
  dsimp only [mappingConeTermProdIso, Iso.trans_hom]
  rw [Category.assoc, hb]
  apply ext_from_X φ (q + 1) q rfl
  · simp only [← Category.assoc, inlX_XIsoBiprod_hom, biprod.inl_snd, inlX_sndX]
  · simp only [← Category.assoc, inrX_XIsoBiprod_hom, biprod.inr_snd, inrX_sndX]

/-- First component of the actual cone differential. -/
lemma mappingConeTermProdIso_d_fst (q : ℤ) (x : (CochainComplex.mappingCone φ).X q) :
    ((mappingConeTermProdIso φ (q + 1)).hom
      ((CochainComplex.mappingCone φ).d q (q + 1) x)).1 =
      -(K.d (q + 1) (q + 1 + 1) ((mappingConeTermProdIso φ q).hom x).1) := by
  have h := d_fstX φ q (q + 1) (q + 1 + 1) rfl rfl
  rw [← mappingConeTermProdIso_fst φ (q + 1), ← mappingConeTermProdIso_fst φ q] at h
  exact congrArg (fun f => f.hom x) h

/-- Second component of the actual cone differential, including its cross term. -/
lemma mappingConeTermProdIso_d_snd (q : ℤ) (x : (CochainComplex.mappingCone φ).X q) :
    ((mappingConeTermProdIso φ (q + 1)).hom
      ((CochainComplex.mappingCone φ).d q (q + 1) x)).2 =
      φ.f (q + 1) ((mappingConeTermProdIso φ q).hom x).1 +
        L.d q (q + 1) ((mappingConeTermProdIso φ q).hom x).2 := by
  have h := d_sndX φ q (q + 1) rfl
  rw [← mappingConeTermProdIso_snd φ (q + 1), ← mappingConeTermProdIso_fst φ q,
    ← mappingConeTermProdIso_snd φ q] at h
  exact congrArg (fun f => f.hom x) h

end SerrePositivity
