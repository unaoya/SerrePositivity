module
public import SerrePositivity.HomologicalAlgebra.CochainAugmentationModels
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModule

/-! # The original scalar-extension augmentation on actual projective resolution models -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Compute the original scalar-extension augmentation by the actual mapped chain map. -/
lemma derivedModuleBaseChangeAugmentation_resolution_homotopy
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (derivedModuleBaseChangeAugmentation φ).app M =
      (chainDerivedRealization S).map
          (P.isoLeftDerivedToHomotopyCategoryObj (ModuleCat.extendScalars φ)).hom ≫
        (chainDerivedRealization S).map ((HomotopyCategory.quotient _ _).map
          (mappedProjectiveResolutionAugmentation (ModuleCat.extendScalars φ) P)) ≫
        (chainDerivedRealizationSingleNatIso S).hom.app
          ((ModuleCat.extendScalars φ).obj M) := by
  let F := ModuleCat.extendScalars φ
  let K := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  let e := P.isoLeftDerivedToHomotopyCategoryObj F
  let h := (ChainComplex.isoHomologyι₀ K).hom ≫ P.fromLeftDerivedZero' F
  have hn := (chainDerivedAugmentation S).naturality e.hom
  dsimp only [Functor.comp_map] at hn
  change (chainDerivedAugmentation S).app (F.leftDerivedToHomotopyCategory.obj M) ≫
    (DerivedCategory.singleFunctor (ModuleCat S) 0).map
      (F.fromLeftDerivedZero.app M) = _
  rw [P.fromLeftDerivedZero_eq F]
  change (chainDerivedAugmentation S).app (F.leftDerivedToHomotopyCategory.obj M) ≫
    (DerivedCategory.singleFunctor (ModuleCat S) 0).map
      ((HomotopyCategory.homologyFunctor (ModuleCat S) (.down ℕ) 0).map e.hom ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat S) (.down ℕ) 0).hom.app K ≫
          h) = _
  rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
  erw [chainDerivedAugmentation_quotient_postcomp K (F.obj M) h]
  dsimp only [h, K, F]
  rw [← mappedProjectiveResolutionAugmentation_eq_projection]

/-- An arbitrary original module resolution computes the scalar-extension augmentation in D(S). -/
lemma derivedModuleBaseChangeResolutionIso_augmentation
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (derivedModuleBaseChangeAugmentation φ).app M =
      (derivedModuleBaseChangeResolutionIso φ P).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.extendMap
          (mappedProjectiveResolutionAugmentation (ModuleCat.extendScalars φ) P) embUp) ≫
        DerivedCategory.Q.map ((extendChainSingleNatIso S).hom.app
          ((ModuleCat.extendScalars φ).obj M)) := by
  let F := ModuleCat.extendScalars φ
  let K := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  let ε := mappedProjectiveResolutionAugmentation F P
  have hn := (chainDerivedRealizationComplexNatIso S).hom.naturality ε
  simp only [Functor.comp_map, ComplexShape.Embedding.extendFunctor_map] at hn
  have hs : (chainDerivedRealizationSingleNatIso S).hom.app (F.obj M) =
      (chainDerivedRealizationComplexNatIso S).hom.app
          ((HomologicalComplex.single (ModuleCat S) (.down ℕ) 0).obj (F.obj M)) ≫
        DerivedCategory.Q.map ((extendChainSingleNatIso S).hom.app (F.obj M)) := by
    simp only [chainDerivedRealizationSingleNatIso, Iso.trans_hom, NatTrans.comp_app,
      Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp]
  rw [derivedModuleBaseChangeAugmentation_resolution_homotopy φ P, hs]
  change (chainDerivedRealization S).map (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
    (chainDerivedRealization S).map ((HomotopyCategory.quotient _ _).map ε) ≫
    (chainDerivedRealizationComplexNatIso S).hom.app _ ≫ _ =
    ((chainDerivedRealization S).map (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
      (chainDerivedRealizationComplexNatIso S).hom.app K) ≫ _ ≫ _
  simp only [Category.assoc]
  rw [← Category.assoc ((chainDerivedRealization S).map
    ((HomotopyCategory.quotient _ _).map ε)), hn, Category.assoc]

/-- The established complex-level augmentation uses its original cochain resolution map. -/
lemma boundedAboveDerivedBaseChangeModuleAugmentation_chosen_models (M : ModuleCat.{u} R) :
    (boundedAboveDerivedBaseChangeModuleAugmentation φ).app M =
      (boundedAboveDerivedBaseChangeModelIso φ (boundedAboveDerivedSingleFunctor.obj M)
        (projectiveResolutionDerivedModel (projectiveResolution M))).hom ≫
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
          (projectiveResolutionCochainAugmentation (projectiveResolution M)) ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app M) := by
  change (boundedAboveDerivedBaseChangeModuleIso φ M).hom ≫
    (derivedModuleBaseChangeAugmentation φ).app M = _
  rw [derivedModuleBaseChangeResolutionIso_augmentation φ (projectiveResolution M)]
  simp only [boundedAboveDerivedBaseChangeModuleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Functor.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  exact mapExtendIso_resolution_augmentation (ModuleCat.extendScalars φ) (projectiveResolution M)

/-- Every actual projective model computes the same original base-change augmentation. -/
lemma boundedAboveDerivedBaseChangeModuleAugmentation_projective_models
    {M : ModuleCat.{u} R}
    (P : BoundedAboveDerivedModel (boundedAboveDerivedSingleFunctor.obj M).obj)
    (εP : P.complex ⟶ cochainSingleZero M)
    (hεP : DerivedCategory.Q.map εP = P.iso.hom) :
    (boundedAboveDerivedBaseChangeModuleAugmentation φ).app M =
      (boundedAboveDerivedBaseChangeModelIso φ (boundedAboveDerivedSingleFunctor.obj M) P).hom ≫
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map εP ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app M) := by
  let F := ModuleCat.extendScalars φ
  let P₀ := projectiveResolutionDerivedModel (projectiveResolution M)
  let f := P.map P₀ (𝟙 _)
  have hf : Homotopy (f ≫ projectiveResolutionCochainAugmentation (projectiveResolution M))
      εP := by
    apply homotopyOfDerivedMapEq
    rw [Functor.map_comp]
    change DerivedCategory.Q.map f ≫ P₀.iso.hom = DerivedCategory.Q.map εP
    rw [P.map_naturality, Category.comp_id, hεP]
  have hn := boundedAboveLeftDerivedModelIso_naturality F P P₀
    (𝟙 (boundedAboveDerivedSingleFunctor.obj M)) f
    (P.map_naturality P₀ (𝟙 _))
  have hi := congrArg (fun t => t.hom)
    ((boundedAboveLeftDerived F).map_id (boundedAboveDerivedSingleFunctor.obj M))
  rw [hi] at hn
  change 𝟙 _ ≫ _ = _ at hn
  rw [Category.id_comp] at hn
  rw [boundedAboveDerivedBaseChangeModuleAugmentation_chosen_models]
  change (boundedAboveDerivedBaseChangeModelIso φ _ P₀).hom ≫ _ = _
  erw [hn, Category.assoc, ← Functor.map_comp]
  congr 1
  apply DerivedCategory.Q_map_eq_of_homotopy (ModuleCat S)
  rw [← Functor.map_comp_assoc]
  exact (F.mapHomotopy hf).compRight _

end SerrePositivity
