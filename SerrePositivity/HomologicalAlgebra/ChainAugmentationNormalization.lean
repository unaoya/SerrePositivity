module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleResolution

/-! # Normalize the standard augmentation on actual chain resolution models -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The chain-level augmentation of an additive functor applied to a module resolution. -/
def mappedProjectiveResolutionAugmentation
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (F.mapHomologicalComplex (.down ℕ)).obj P.complex ⟶
      (HomologicalComplex.single (ModuleCat.{u} S) (.down ℕ) 0).obj (F.obj M) :=
  HomologicalComplex.mkHomToSingle (F.map (P.π.f 0)) (by
    intro i hi
    have hi : i = 1 := by dsimp at hi; omega
    subst i
    change F.map (P.complex.d 1 0) ≫ F.map (P.π.f 0) = 0
    rw [← CategoryTheory.Functor.map_comp, P.complex_d_comp_π_f_zero,
      CategoryTheory.Functor.map_zero])

/-- Its homology-normalized form is precisely the standard zero-derived augmentation. -/
lemma mappedProjectiveResolutionAugmentation_eq_projection
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    mappedProjectiveResolutionAugmentation F P =
      chainHomologyZeroProjection S ((F.mapHomologicalComplex (.down ℕ)).obj P.complex) ≫
        (HomologicalComplex.single (ModuleCat.{u} S) (.down ℕ) 0).map
          ((ChainComplex.isoHomologyι₀ _).hom ≫ P.fromLeftDerivedZero' F) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [mappedProjectiveResolutionAugmentation, HomologicalComplex.comp_f,
    chainHomologyZeroProjection, HomologicalComplex.mkHomToSingle_f,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]

/-- On an actual chain model, the realized augmentation uses the actual chain projection,
with the quotient homology identification made explicit. -/
lemma chainDerivedAugmentation_quotient
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (chainDerivedAugmentation R).app ((HomotopyCategory.quotient _ _).obj K) =
      (chainDerivedRealization R).map
        ((HomotopyCategory.quotient _ _).map (chainHomologyZeroProjection R K)) ≫
      (chainDerivedRealizationSingleNatIso R).hom.app (K.homology 0) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.down ℕ) 0).inv.app K) := by
  simp only [chainDerivedAugmentation, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
    Category.id_comp]
  change (chainDerivedRealization R).map
    ((HomotopyCategory.quotient _ _).map (chainHomologyZeroProjection R K) ≫
      (HomologicalComplex.single (ModuleCat.{u} R) (.down ℕ) 0 ⋙
        HomotopyCategory.quotient _ _).map
          ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.down ℕ) 0).inv.app K)) ≫
      (chainDerivedRealizationSingleNatIso R).hom.app _ = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (chainDerivedRealizationSingleNatIso R).hom.naturality
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.down ℕ) 0).inv.app K)
  exact congrArg (fun h => (chainDerivedRealization R).map
    ((HomotopyCategory.quotient _ _).map (chainHomologyZeroProjection R K)) ≫ h) hn

/-- After the quotient homology normalization, every realized chain augmentation
is the realization of its actual chain projection followed by the specified homology map. -/
lemma chainDerivedAugmentation_quotient_postcomp
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (M : ModuleCat.{u} R)
    (h : K.homology 0 ⟶ M) :
    (chainDerivedAugmentation R).app ((HomotopyCategory.quotient _ _).obj K) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
          ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.down ℕ) 0).hom.app K ≫ h) =
      (chainDerivedRealization R).map ((HomotopyCategory.quotient _ _).map
        (chainHomologyZeroProjection R K ≫
          (HomologicalComplex.single (ModuleCat.{u} R) (.down ℕ) 0).map h)) ≫
        (chainDerivedRealizationSingleNatIso R).hom.app M := by
  rw [chainDerivedAugmentation_quotient]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp]
  have hn := (chainDerivedRealizationSingleNatIso R).hom.naturality h
  exact congrArg (fun k => (chainDerivedRealization R).map
    ((HomotopyCategory.quotient _ _).map (chainHomologyZeroProjection R K)) ≫ k) hn.symm

/-- The established tensor augmentation is computed by the actual augmented resolution,
including the chosen-resolution comparison in the homotopy category. -/
lemma realizedDerivedTensorAugmentation_resolution_homotopy
    (V : ModuleCat.{u} R) {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (realizedDerivedTensorAugmentation R V).app M =
      (chainDerivedRealization R).map
          (P.isoLeftDerivedToHomotopyCategoryObj (MonoidalCategory.tensorLeft V)).hom ≫
        (chainDerivedRealization R).map ((HomotopyCategory.quotient _ _).map
          (mappedProjectiveResolutionAugmentation (MonoidalCategory.tensorLeft V) P)) ≫
        (chainDerivedRealizationSingleNatIso R).hom.app
          ((MonoidalCategory.tensorLeft V).obj M) := by
  let F := MonoidalCategory.tensorLeft V
  let K := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  let e := P.isoLeftDerivedToHomotopyCategoryObj F
  let h := (ChainComplex.isoHomologyι₀ K).hom ≫ P.fromLeftDerivedZero' F
  have hn := (chainDerivedAugmentation R).naturality e.hom
  dsimp only [Functor.comp_map] at hn
  change (chainDerivedAugmentation R).app (F.leftDerivedToHomotopyCategory.obj M) ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
      (F.fromLeftDerivedZero.app M) = _
  rw [P.fromLeftDerivedZero_eq F]
  change (chainDerivedAugmentation R).app (F.leftDerivedToHomotopyCategory.obj M) ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
      ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.down ℕ) 0).map e.hom ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.down ℕ) 0).hom.app K ≫
          h) = _
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
  erw [chainDerivedAugmentation_quotient_postcomp K (F.obj M) h]
  dsimp only [h, K, F]
  rw [← mappedProjectiveResolutionAugmentation_eq_projection]

/-- Compute the established tensor augmentation on an arbitrary actual projective resolution
as the localization of its extended chain augmentation. -/
lemma realizedDerivedTensorResolutionIso_augmentation
    (V : ModuleCat.{u} R) {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (realizedDerivedTensorAugmentation R V).app M =
      (realizedDerivedTensorResolutionIso V P).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.extendMap
          (mappedProjectiveResolutionAugmentation (MonoidalCategory.tensorLeft V) P) embUp) ≫
        DerivedCategory.Q.map ((extendChainSingleNatIso R).hom.app
          ((MonoidalCategory.tensorLeft V).obj M)) := by
  let F := MonoidalCategory.tensorLeft V
  let K := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  let ε := mappedProjectiveResolutionAugmentation F P
  have hn := (chainDerivedRealizationComplexNatIso R).hom.naturality ε
  simp only [Functor.comp_map, ComplexShape.Embedding.extendFunctor_map] at hn
  have hs : (chainDerivedRealizationSingleNatIso R).hom.app (F.obj M) =
      (chainDerivedRealizationComplexNatIso R).hom.app
          ((HomologicalComplex.single (ModuleCat.{u} R) (.down ℕ) 0).obj (F.obj M)) ≫
        DerivedCategory.Q.map ((extendChainSingleNatIso R).hom.app (F.obj M)) := by
    simp only [chainDerivedRealizationSingleNatIso, Iso.trans_hom, NatTrans.comp_app,
      Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp]
  rw [realizedDerivedTensorAugmentation_resolution_homotopy V P]
  rw [hs]
  change (chainDerivedRealization R).map (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
    (chainDerivedRealization R).map ((HomotopyCategory.quotient _ _).map ε) ≫
    (chainDerivedRealizationComplexNatIso R).hom.app _ ≫ _ =
    ((chainDerivedRealization R).map (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
      (chainDerivedRealizationComplexNatIso R).hom.app K) ≫ _ ≫ _
  simp only [Category.assoc]
  rw [← Category.assoc ((chainDerivedRealization R).map
    ((HomotopyCategory.quotient _ _).map ε)), hn, Category.assoc]

end SerrePositivity
