module
public import SerrePositivity.HomologicalAlgebra.CochainTensorBaseChange

/-! # Naturality of the total tensor base-change comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R S : Type u} [CommRing R] [CommRing S]

@[reassoc]
lemma cochainTensorMap_homogeneous
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ (cochainTensorMap f g).f n =
      (f.f i ⊗ₘ g.f j) ≫ ιTensorObj P' Q' i j n h :=
  ιTensorObj_cochainTensorMap f g i j n h

/-- The tensor base-change comparison is natural in both chain maps. -/
lemma cochainTensorBaseChangeIso_naturality (φ : R →+* S)
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map (cochainTensorMap f g) ≫
        (cochainTensorBaseChangeIso φ P' Q').hom =
      (cochainTensorBaseChangeIso φ P Q).hom ≫ cochainTensorMap
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map f)
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map g) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorBaseChange_hom_ext φ P Q
  intro i j h
  change (ModuleCat.extendScalars φ).map (ιTensorObj P Q i j n h) ≫
      (ModuleCat.extendScalars φ).map ((cochainTensorMap f g).f n) ≫
      (cochainTensorBaseChangeIso φ P' Q').hom.f n =
    (ModuleCat.extendScalars φ).map (ιTensorObj P Q i j n h) ≫
      (cochainTensorBaseChangeIso φ P Q).hom.f n ≫ _
  rw [← CategoryTheory.Functor.map_comp_assoc, cochainTensorMap_homogeneous,
    CategoryTheory.Functor.map_comp, Category.assoc]
  change _ ≫ _ ≫ (cochainTensorBaseChangeXIso φ P' Q' n).hom =
    _ ≫ (cochainTensorBaseChangeXIso φ P Q n).hom ≫ _
  rw [map_ι_cochainTensorBaseChangeXIso, map_ι_cochainTensorBaseChangeXIso_assoc,
    cochainTensorMap_homogeneous]
  exact (Functor.OplaxMonoidal.δ_natural_assoc
    (ModuleCat.extendScalars φ) (f.f i) (g.f j) _).symm

end SerrePositivity
