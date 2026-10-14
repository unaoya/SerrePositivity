module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorRealization

/-! # Resolution computation of the existing realized derived tensor -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Compute the existing derived tensor with any projective resolution of the right module. -/
def realizedDerivedTensorResolutionIso (V : ModuleCat.{u} R)
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (realizedDerivedTensorFunctor R V).obj M ≅ DerivedCategory.Q.obj
      (((MonoidalCategory.tensorLeft V).mapHomologicalComplex (.down ℕ)).obj
        P.complex |>.extend embUp) :=
  (chainDerivedRealization R).mapIso
    (P.isoLeftDerivedToHomotopyCategoryObj (MonoidalCategory.tensorLeft V)) ≪≫
    (chainDerivedRealizationComplexNatIso R).app _

/-- The computation is natural in the right module and its chosen resolution lift. -/
@[reassoc] theorem realizedDerivedTensorResolutionIso_naturality (V : ModuleCat.{u} R)
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (realizedDerivedTensorFunctor R V).map f ≫ (realizedDerivedTensorResolutionIso V Q).hom =
      (realizedDerivedTensorResolutionIso V P).hom ≫ DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          (((MonoidalCategory.tensorLeft V).mapHomologicalComplex (.down ℕ)).map
            (ProjectiveResolution.lift f P Q)) embUp) := by
  have hp := ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality
    f P Q (ProjectiveResolution.lift f P Q) (by simp) (MonoidalCategory.tensorLeft V)
  have hn := (chainDerivedRealizationComplexNatIso R).hom.naturality
    (((MonoidalCategory.tensorLeft V).mapHomologicalComplex (.down ℕ)).map
      (ProjectiveResolution.lift f P Q))
  simp only [Functor.comp_map] at hn
  change (chainDerivedRealization R).map _ ≫ (chainDerivedRealization R).map _ ≫ _ = _
  rw [← Functor.map_comp_assoc, hp, Functor.map_comp, Category.assoc]
  simpa only [realizedDerivedTensorResolutionIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.comp_map, ComplexShape.Embedding.extendFunctor_map,
    Category.assoc] using congrArg (fun g ↦ (chainDerivedRealization R).map
      (P.isoLeftDerivedToHomotopyCategoryObj (MonoidalCategory.tensorLeft V)).hom ≫ g) hn

/-- The computation also respects maps of the unresolved left module. -/
@[reassoc] theorem realizedDerivedTensorResolutionIso_naturality_left
    {V W : ModuleCat.{u} R} (f : V ⟶ W) {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (realizedDerivedTensorMapLeft R f).app M ≫ (realizedDerivedTensorResolutionIso W P).hom =
      (realizedDerivedTensorResolutionIso V P).hom ≫ DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          ((NatTrans.mapHomologicalComplex
            ((MonoidalCategory.tensoringLeft (ModuleCat R)).map f) (.down ℕ)).app P.complex)
          embUp) := by
  let α := (MonoidalCategory.tensoringLeft (ModuleCat R)).map f
  have hp := ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq α P
  have hn := (chainDerivedRealizationComplexNatIso R).hom.naturality
    ((NatTrans.mapHomologicalComplex α (.down ℕ)).app P.complex)
  simp only [Functor.comp_map] at hn
  change (chainDerivedRealization R).map ((NatTrans.leftDerivedToHomotopyCategory α).app M) ≫
    (chainDerivedRealization R).map (P.isoLeftDerivedToHomotopyCategoryObj
      (MonoidalCategory.tensorLeft W)).hom ≫ _ = _
  rw [hp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [Category.comp_id, Functor.map_comp, Category.assoc]
  simpa only [realizedDerivedTensorResolutionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, ComplexShape.Embedding.extendFunctor_map, Category.assoc] using
    congrArg (fun g => (chainDerivedRealization R).map
    (P.isoLeftDerivedToHomotopyCategoryObj (MonoidalCategory.tensorLeft V)).hom ≫ g) hn

end SerrePositivity
