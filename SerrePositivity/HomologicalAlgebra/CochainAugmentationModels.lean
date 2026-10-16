module
public import SerrePositivity.HomologicalAlgebra.ChainAugmentationNormalization
public import SerrePositivity.HomologicalAlgebra.CochainSingleMonoidal
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison

/-! # Compute actual derived tensor augmentations on cochain projective models -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The zero-degree resolution augmentation is the image of the original augmentation,
followed by the canonical additive-functor/single-object comparison. -/
lemma mappedProjectiveResolutionAugmentation_eq_map
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    mappedProjectiveResolutionAugmentation F P =
      (F.mapHomologicalComplex (.down ℕ)).map P.π ≫
        (HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0).hom.app M := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [mappedProjectiveResolutionAugmentation, HomologicalComplex.mkHomToSingle_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Additive functors and extension by zero give the same standard comparison on singles. -/
lemma mapExtendIso_single_comparison
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] (M : ModuleCat.{u} R) :
    (mapExtendIso F ((HomologicalComplex.single (ModuleCat R) (.down ℕ) 0).obj M) embUp).hom ≫
      HomologicalComplex.extendMap
        ((HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0).hom.app M) embUp ≫
      (extendChainSingleNatIso S).hom.app (F.obj M) =
    (F.mapHomologicalComplex (.up ℤ)).map ((extendChainSingleNatIso R).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, mapExtendIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  dsimp only [mapExtendXIso]
  split_ifs with h
  · have H (j : ℕ) (hj : embUp.f j = (0 : ℤ)) :
        (F.mapIso (HomologicalComplex.extendXIso
          ((HomologicalComplex.single (ModuleCat R) (.down ℕ) 0).obj M) embUp hj) ≪≫
          (HomologicalComplex.extendXIso
            ((F.mapHomologicalComplex (.down ℕ)).obj
              ((HomologicalComplex.single (ModuleCat R) (.down ℕ) 0).obj M)) embUp hj).symm).hom ≫
          (HomologicalComplex.extendMap
            ((HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0).hom.app M)
              embUp).f 0 ≫ ((extendChainSingleNatIso S).hom.app (F.obj M)).f 0 =
        ((F.mapHomologicalComplex (.up ℤ)).map
            ((extendChainSingleNatIso R).hom.app M)).f 0 ≫
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M).f 0 := by
      have hj0 : j = 0 := by dsimp [embUp] at hj; omega
      subst j
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        HomologicalComplex.extendMap_f _ embUp (show embUp.f 0 = 0 by rfl),
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        extendChainSingleNatIso, NatIso.ofComponents_hom_app,
        HomologicalComplex.extendSingleIso_hom_f,
        Functor.mapHomologicalComplex_map_f, CategoryTheory.Functor.map_comp, Category.assoc,
        Functor.comp_obj, Iso.inv_hom_id_assoc]
      simp
    exact H _ h.choose_spec
  · exact False.elim (h ⟨0, rfl⟩)

/-- An extended mapped chain augmentation is the ordinary mapped cochain augmentation. -/
lemma mapExtendIso_resolution_augmentation
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (mapExtendIso F P.complex embUp).hom ≫
        HomologicalComplex.extendMap (mappedProjectiveResolutionAugmentation F P) embUp ≫
        (extendChainSingleNatIso S).hom.app (F.obj M) =
      (F.mapHomologicalComplex (.up ℤ)).map (projectiveResolutionCochainAugmentation P) ≫
        (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M := by
  rw [mappedProjectiveResolutionAugmentation_eq_map, HomologicalComplex.extendMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (mapExtendIso F P.complex embUp).hom]
  erw [← mapExtendIso_naturality F embUp P.π]
  rw [Category.assoc]
  erw [mapExtendIso_single_comparison F M]
  simp only [projectiveResolutionCochainAugmentation,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- The one-sided total-to-pointwise tensor comparison respects the actual augmentation. -/
lemma cochainTensorSingleLeftIso_resolution_augmentation
    (M : ModuleCat.{u} R) {N : ModuleCat.{u} R} (P : ProjectiveResolution N) :
    (cochainTensorSingleLeftIso M (extRes P)).hom ≫
        (mapExtendIso (tensorLeft M) P.complex embUp).hom ≫
        HomologicalComplex.extendMap
          (mappedProjectiveResolutionAugmentation (tensorLeft M) P) embUp ≫
        (extendChainSingleNatIso R).hom.app ((tensorLeft M).obj N) =
      cochainTensorMap (𝟙 (cochainSingleZero M)) (projectiveResolutionCochainAugmentation P) ≫
        (cochainSingleTensorIso M N).hom := by
  rw [← Category.assoc, Category.assoc
    ((cochainTensorSingleLeftIso M (extRes P)).hom),
    mapExtendIso_resolution_augmentation]
  rw [← Category.assoc, ← cochainTensorSingleLeftIso_naturality]
  simp only [cochainSingleTensorIso, Iso.trans_hom, Iso.app_hom, Category.assoc]

/-- Compute the actual two-sided derived tensor augmentation on its chosen module resolutions. -/
lemma boundedAboveDerivedTensorModuleAugmentation_chosen_models
    (M N : ModuleCat.{u} R) :
    (boundedAboveDerivedTensorModuleAugmentation M).app N =
      (boundedAboveDerivedTensorModelIso
        (boundedAboveDerivedSingleFunctor.obj M) (boundedAboveDerivedSingleFunctor.obj N)
        (projectiveResolutionDerivedModel (projectiveResolution M))
        (projectiveResolutionDerivedModel (projectiveResolution N))).hom ≫
      DerivedCategory.Q.map
        (cochainTensorMap
          (projectiveResolutionCochainAugmentation (projectiveResolution M))
          (projectiveResolutionCochainAugmentation (projectiveResolution N)) ≫
          (cochainSingleTensorIso M N).hom) := by
  let P := projectiveResolution M
  let Q := projectiveResolution N
  change (boundedAboveDerivedTensorModuleIso M N).hom ≫
    (realizedDerivedTensorAugmentation R M).app N = _
  rw [realizedDerivedTensorResolutionIso_augmentation M Q]
  simp only [Q, boundedAboveDerivedTensorModuleIso, derivedTensorModuleModelIso,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  erw [cochainTensorSingleLeftIso_resolution_augmentation M (projectiveResolution N)]
  rw [← Category.assoc, cochainTensorMap_comp]
  simp only [Category.comp_id, Category.id_comp]

/-- The same actual two-sided tensor augmentation is computed on any two module resolutions. -/
lemma boundedAboveDerivedTensorModuleAugmentation_models
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (boundedAboveDerivedTensorModuleAugmentation M).app N =
      (boundedAboveDerivedTensorModelIso
        (boundedAboveDerivedSingleFunctor.obj M) (boundedAboveDerivedSingleFunctor.obj N)
        (projectiveResolutionDerivedModel P) (projectiveResolutionDerivedModel Q)).hom ≫
      DerivedCategory.Q.map
        (cochainTensorMap (projectiveResolutionCochainAugmentation P)
          (projectiveResolutionCochainAugmentation Q) ≫ (cochainSingleTensorIso M N).hom) := by
  have rep {U : ModuleCat.{u} R} (A B : ProjectiveResolution U) :
      DerivedCategory.Q.map (extLift A (𝟙 U) B) ≫
          (projectiveResolutionDerivedModel B).iso.hom =
        (projectiveResolutionDerivedModel A).iso.hom ≫ 𝟙 _ := by
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
      DerivedCategory.Q.map _ ≫ 𝟙 _
    rw [← CategoryTheory.Functor.map_comp,
      projectiveResolutionCochainAugmentation_naturality]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := boundedAboveDerivedTensorModelIso_naturality
    (projectiveResolutionDerivedModel P)
    (projectiveResolutionDerivedModel (projectiveResolution M))
    (projectiveResolutionDerivedModel Q)
    (projectiveResolutionDerivedModel (projectiveResolution N))
    (𝟙 (boundedAboveDerivedSingleFunctor.obj M))
    (𝟙 (boundedAboveDerivedSingleFunctor.obj N))
    (extLift P (𝟙 M) (projectiveResolution M))
    (extLift Q (𝟙 N) (projectiveResolution N)) (rep _ _) (rep _ _)
  simp only [← CategoryTheory.prod_id', CategoryTheory.Functor.map_id] at hn
  rw [ObjectProperty.FullSubcategory.id_hom, Category.id_comp] at hn
  rw [boundedAboveDerivedTensorModuleAugmentation_chosen_models, hn, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  rw [← Category.assoc, cochainTensorMap_comp,
    projectiveResolutionCochainAugmentation_naturality,
    projectiveResolutionCochainAugmentation_naturality]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

end SerrePositivity
