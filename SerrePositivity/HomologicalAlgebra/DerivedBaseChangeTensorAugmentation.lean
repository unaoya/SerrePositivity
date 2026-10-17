module

public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeAugmentationComparison
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationModels
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor

/-! # 標準底変換 augmentation と標準 tensor augmentation の一致

選択した射影モデルの任意性を、既存のモデル上の augmentation 計算で処理する。
平坦性・完備性・正則性は要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)

/-- 零次数の底変換・係数制限・通常 tensor 比較は同じ標準写像を与える。 -/
lemma restrictedBaseChangeComplexIso_single_augmentation (M : ModuleCat.{u} R) :
    (restrictedBaseChangeComplexIso φ (cochainSingleZero M)).hom ≫
      (cochainSingleTensorIso (baseChangeScalarModule φ) M).hom =
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars φ) (.up ℤ) 0).hom.app
          ((ModuleCat.extendScalars φ).obj M) ≫
      (CochainComplex.singleFunctor (ModuleCat R) 0).map
        ((extendRestrictTensorIso φ).hom.app M) := by
  unfold restrictedBaseChangeComplexIso cochainSingleTensorIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.to_single_hom_ext
  simp [Functor.mapHomologicalComplexCompIso]
  have hn := (extendRestrictTensorIso φ).hom.naturality
    (singleObjXSelf (.up ℤ) 0 M).hom
  change (ModuleCat.restrictScalars φ).map
      ((ModuleCat.extendScalars φ).map (singleObjXSelf (.up ℤ) 0 M).hom) ≫
      (extendRestrictTensorIso φ).hom.app M =
    (extendRestrictTensorIso φ).hom.app ((cochainSingleZero M).X 0) ≫
      (baseChangeScalarModule φ ◁ (singleObjXSelf (.up ℤ) 0 M).hom) at hn
  simpa only [CochainComplex.singleFunctor, single_map_f_self, Category.assoc,
    Iso.inv_hom_id_assoc] using congrArg (fun k => k ≫
      (singleObjXSelf (.up ℤ) 0 (baseChangeScalarModule φ ⊗ M)).inv) hn.symm

/-- 任意の複体から零次数加群への射について、二つの通常 augmentation は一致する。 -/
lemma restrictedBaseChangeComplexIso_augmentation
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (M : ModuleCat.{u} R)
    (ε : K ⟶ cochainSingleZero M) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map ε) ≫
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars φ) (.up ℤ) 0).hom.app
          ((ModuleCat.extendScalars φ).obj M) ≫
      (CochainComplex.singleFunctor (ModuleCat R) 0).map
        ((extendRestrictTensorIso φ).hom.app M) =
    (restrictedBaseChangeComplexIso φ K).hom ≫
      cochainTensorMap (𝟙 (cochainSingleZero (baseChangeScalarModule φ))) ε ≫
      (cochainSingleTensorIso (baseChangeScalarModule φ) M).hom := by
  rw [← restrictedBaseChangeComplexIso_single_augmentation]
  rw [← Category.assoc, restrictedBaseChangeComplexIso_naturality, Category.assoc]

/-- 一方の射影解消を外した実 tensor モデルでも元の augmentation を保つ。 -/
lemma derivedScalarTensorModelIso_augmentation (M : ModuleCat.{u} R)
    (ε : (boundedAboveDerivedChosenModel (boundedAboveDerivedSingleFunctor.obj M)).complex ⟶
      cochainSingleZero M)
    (hε : DerivedCategory.Q.map ε =
      (boundedAboveDerivedChosenModel (boundedAboveDerivedSingleFunctor.obj M)).iso.hom) :
    (derivedScalarTensorModelIso φ (boundedAboveDerivedSingleFunctor.obj M)).hom ≫
      DerivedCategory.Q.map
        (cochainTensorMap (𝟙 (cochainSingleZero (baseChangeScalarModule φ))) ε ≫
          (cochainSingleTensorIso (baseChangeScalarModule φ) M).hom) =
    (boundedAboveDerivedTensorModuleAugmentation (baseChangeScalarModule φ)).app M := by
  rw [boundedAboveDerivedTensorModuleAugmentation_projective_models
    (derivedBaseChangeScalarModel φ)
    (boundedAboveDerivedChosenModel (boundedAboveDerivedSingleFunctor.obj M))
    (projectiveResolutionCochainAugmentation (projectiveResolution (baseChangeScalarModule φ)))
    ε rfl hε]
  simp only [derivedScalarTensorModelIso, Iso.trans_hom, asIso_hom, Category.assoc,
    ← Functor.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  rw [← Category.assoc, cochainTensorMap_comp]
  simp only [Category.comp_id, Category.id_comp]

/-- 底変換と tensor の実比較は、両方の元の標準 augmentation と可換。
環写像の平坦性・加群の有限性・完備性は不要。 -/
theorem boundedAboveDerivedBaseChangeTensorIso_augmentation (M : ModuleCat.{u} R) :
    (derivedRestrictScalars φ).map
        ((boundedAboveDerivedBaseChangeModuleAugmentation φ).app M) ≫
      (derivedRestrictScalarsSingleIso φ 0).hom.app ((ModuleCat.extendScalars φ).obj M) ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map ((extendRestrictTensorIso φ).hom.app M) =
    (boundedAboveDerivedBaseChangeTensorIso φ (boundedAboveDerivedSingleFunctor.obj M)).hom.hom ≫
      (boundedAboveDerivedTensorModuleAugmentation (baseChangeScalarModule φ)).app M := by
  let X := boundedAboveDerivedSingleFunctor.obj M
  let Q := boundedAboveDerivedChosenModel X
  let Q₀ := projectiveResolutionDerivedModel (projectiveResolution M)
  let ε := Q.map Q₀ (𝟙 _) ≫ projectiveResolutionCochainAugmentation (projectiveResolution M)
  have hε : DerivedCategory.Q.map ε = Q.iso.hom := by
    rw [Functor.map_comp]
    change DerivedCategory.Q.map (Q.map Q₀ (𝟙 _)) ≫ Q₀.iso.hom = Q.iso.hom
    rw [Q.map_naturality, Category.comp_id]
  have ha := boundedAboveDerivedBaseChangeModuleAugmentation_projective_models φ Q ε hε
  rw [boundedAboveDerivedBaseChangeModelIso_chosen_hom, Category.id_comp] at ha
  let F := ModuleCat.extendScalars φ
  let U := ModuleCat.restrictScalars φ
  let a := (F.mapHomologicalComplex (.up ℤ)).map ε ≫
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M
  have hs : (derivedRestrictScalarsSingleIso φ 0).hom.app (F.obj M) =
      (derivedRestrictScalarsFactors φ).hom.app (cochainSingleZero (F.obj M)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app (F.obj M)) := by
    apply (cancel_epi ((derivedRestrictScalarsFactors φ).inv.app
      (cochainSingleZero (F.obj M)))).mp
    simp only [derivedRestrictScalarsSingleIso, derivedRestrictScalarsFactors,
      Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rfl
  have hm : (restrictedDerivedBaseChangeModelIso φ X).hom =
      (derivedRestrictScalarsFactors φ).hom.app (baseChange φ Q.complex) ≫
        DerivedCategory.Q.map (restrictedBaseChangeComplexIso φ Q.complex).hom := by
    change ((derivedRestrictScalars φ).map (𝟙 (DerivedCategory.Q.obj (baseChange φ Q.complex))) ≫
        (derivedRestrictScalarsFactors φ).hom.app (baseChange φ Q.complex)) ≫
        DerivedCategory.Q.map (restrictedBaseChangeComplexIso φ Q.complex).hom = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (derivedRestrictScalarsFactors φ).hom.naturality a
  change (derivedRestrictScalars φ).map (DerivedCategory.Q.map a) ≫
      (derivedRestrictScalarsFactors φ).hom.app (cochainSingleZero (F.obj M)) =
    (derivedRestrictScalarsFactors φ).hom.app (baseChange φ Q.complex) ≫
      DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map a) at hn
  rw [← derivedScalarTensorModelIso_augmentation φ M ε hε]
  simp only [boundedAboveDerivedBaseChangeTensorIso, ObjectProperty.isoMk,
    ObjectProperty.homMk_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [ha, hs, hm]
  change (derivedRestrictScalars φ).map (DerivedCategory.Q.map a) ≫ _ = _
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  simp only [← Functor.map_comp]
  congr 1
  change _ ≫ _ ≫ DerivedCategory.Q.map
    ((CochainComplex.singleFunctor (ModuleCat R) 0).map
      ((extendRestrictTensorIso φ).hom.app M)) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  simp only [a, Functor.map_comp, Category.assoc]
  exact restrictedBaseChangeComplexIso_augmentation φ M ε

end SerrePositivity
