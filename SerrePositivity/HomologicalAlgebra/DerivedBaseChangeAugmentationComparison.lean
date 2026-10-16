module
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeAugmentationModels
public import SerrePositivity.HomologicalAlgebra.CochainTensorBaseChangeSingle
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationModels
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-! # Scalar extension of the original augmentation from an arbitrary projective model -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Scalar extension of a map to a discrete module uses its original projective-model chain map. -/
lemma boundedAboveDerivedBaseChangeModuleAugmentation_map_model
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (P : BoundedAboveDerivedModel X.obj)
    (M : ModuleCat.{u} R) (g : X ⟶ boundedAboveDerivedSingleFunctor.obj M)
    (ε : P.complex ⟶ cochainSingleZero M)
    (hε : DerivedCategory.Q.map ε = P.iso.hom ≫ g.hom) :
    ((boundedAboveDerivedBaseChange φ).map g).hom ≫
        (boundedAboveDerivedBaseChangeModuleAugmentation φ).app M =
      (boundedAboveDerivedBaseChangeModelIso φ X P).hom ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map ε ≫
            (HomologicalComplex.singleMapHomologicalComplex
              (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app M) := by
  let F := ModuleCat.extendScalars φ
  let P₀ := projectiveResolutionDerivedModel (projectiveResolution M)
  let f := P.map P₀ g.hom
  have hf : Homotopy (f ≫ projectiveResolutionCochainAugmentation (projectiveResolution M))
      ε := by
    apply homotopyOfDerivedMapEq
    rw [Functor.map_comp]
    change DerivedCategory.Q.map f ≫ P₀.iso.hom = DerivedCategory.Q.map ε
    rw [P.map_naturality, hε]
  have hn := boundedAboveLeftDerivedModelIso_naturality F P P₀ g f
    (P.map_naturality P₀ g.hom)
  rw [boundedAboveDerivedBaseChangeModuleAugmentation_chosen_models]
  change ((boundedAboveDerivedBaseChange φ).map g).hom ≫
    ((boundedAboveDerivedBaseChangeModelIso φ _ P₀).hom ≫ _) = _
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  congr 1
  apply DerivedCategory.Q_map_eq_of_homotopy (ModuleCat S)
  rw [← Functor.map_comp_assoc]
  exact (F.mapHomotopy hf).compRight _

/-- The actual tensor base-change map commutes with arbitrary original cochain augmentations. -/
lemma cochainTensorBaseChangeIso_augmentation
    {M N : ModuleCat.{u} R} {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (εP : P ⟶ cochainSingleZero M) (εQ : Q ⟶ cochainSingleZero N) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (cochainTensorMap εP εQ ≫ (cochainSingleTensorIso M N).hom) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app (M ⊗ N) ≫
      (CochainComplex.singleFunctor (ModuleCat S) 0).map
        (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ) M N) =
    (cochainTensorBaseChangeIso φ P Q).hom ≫
      cochainTensorMap
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map εP ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app M)
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map εQ ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app N) ≫
      (cochainSingleTensorIso ((ModuleCat.extendScalars φ).obj M)
        ((ModuleCat.extendScalars φ).obj N)).hom := by
  rw [Functor.map_comp, Category.assoc, ← cochainTensorBaseChangeIso_single]
  rw [← Category.assoc, cochainTensorBaseChangeIso_naturality, Category.assoc]
  rw [← cochainTensorMap_comp]
  simp only [Category.assoc]

/-- Comparing the actual chosen base-change model with itself induces the original identity. -/
lemma boundedAboveDerivedBaseChangeModelIso_chosen_hom
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    (boundedAboveDerivedBaseChangeModelIso φ X (boundedAboveDerivedChosenModel X)).hom = 𝟙 _ := by
  let P := boundedAboveDerivedChosenModel X
  change DerivedCategory.Q.map (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
    (P.map P (𝟙 X.obj))) = _
  rw [DerivedCategory.Q_map_eq_of_homotopy (ModuleCat S)
      ((ModuleCat.extendScalars φ).mapHomotopy P.mapIdHomotopy),
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-- The original chosen tensor model comparison also induces the identity. -/
lemma boundedAboveDerivedTensorModelIso_chosen_hom
    (X Y : DerivedCategory.Minus (ModuleCat.{u} R)) :
    (boundedAboveDerivedTensorModelIso X Y
      (boundedAboveDerivedChosenModel X) (boundedAboveDerivedChosenModel Y)).hom = 𝟙 _ := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  change DerivedCategory.Q.map (cochainTensorMap (P.map P (𝟙 X.obj))
    (Q.map Q (𝟙 Y.obj))) = _
  rw [DerivedCategory.Q_map_eq_of_homotopy (ModuleCat R)
    ((cochainTensorHomotopyLeft P.mapIdHomotopy _).trans
      (cochainTensorHomotopyRight (𝟙 _) Q.mapIdHomotopy))]
  rw [cochainTensorMap_id, CategoryTheory.Functor.map_id]
  rfl

/-- Under the factor's Tor condition, the same complex resolves its ordinary scalar extension. -/
def boundedAboveDerivedBaseChangeSingleModel (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing φ M) :
    BoundedAboveDerivedModel
      (boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj M)).obj := by
  let P := boundedAboveDerivedBaseChangeModel φ (boundedAboveDerivedSingleFunctor.obj M)
  exact
    { complex := P.complex
      bound := P.bound
      bounded := P.bounded
      projective := P.projective
      iso := P.iso ≪≫ DerivedCategory.Minus.ι.mapIso
        (boundedAboveDerivedBaseChangeModuleAugmentationIso φ M hM) }

/-- Its original scalar-extended augmentation induces exactly that ordinary-factor model iso. -/
lemma boundedAboveDerivedBaseChangeSingleModel_augmentation
    (M : ModuleCat.{u} R) (hM : scalarExtensionTorVanishing φ M)
    (ε : (boundedAboveDerivedChosenModel (boundedAboveDerivedSingleFunctor.obj M)).complex ⟶
      cochainSingleZero M)
    (hε : DerivedCategory.Q.map ε =
      (boundedAboveDerivedChosenModel (boundedAboveDerivedSingleFunctor.obj M)).iso.hom) :
    DerivedCategory.Q.map
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map ε ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app M) =
      (boundedAboveDerivedBaseChangeSingleModel φ M hM).iso.hom := by
  have h := boundedAboveDerivedBaseChangeModuleAugmentation_projective_models φ
    (boundedAboveDerivedChosenModel (boundedAboveDerivedSingleFunctor.obj M)) ε hε
  rw [boundedAboveDerivedBaseChangeModelIso_chosen_hom, Category.id_comp] at h
  change _ = 𝟙 _ ≫ (boundedAboveDerivedBaseChangeModuleAugmentation φ).app M
  rw [Category.id_comp]
  exact h.symm

/-- Tensor base change to both ordinary factors retains the original standard augmentation. -/
lemma boundedAboveDerivedTensorBaseChangeModuleIso_augmentation
    (M N : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing φ M) (hN : scalarExtensionTorVanishing φ N) :
    (boundedAboveDerivedTensorBaseChangeModuleIso φ M N hM hN).hom.hom ≫
        (boundedAboveDerivedTensorModuleAugmentation ((ModuleCat.extendScalars φ).obj M)).app
          ((ModuleCat.extendScalars φ).obj N) =
      ((boundedAboveDerivedBaseChange φ).map
        (ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation M).app N))).hom ≫
        (boundedAboveDerivedBaseChangeModuleAugmentation φ).app (M ⊗ N) ≫
        (DerivedCategory.singleFunctor (ModuleCat S) 0).map
          (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ) M N) := by
  let F := ModuleCat.extendScalars φ
  let XM := boundedAboveDerivedSingleFunctor.obj M
  let XN := boundedAboveDerivedSingleFunctor.obj N
  let P := boundedAboveDerivedChosenModel XM
  let Q := boundedAboveDerivedChosenModel XN
  have aug (U : ModuleCat.{u} R) :
      ∃ ε : (boundedAboveDerivedChosenModel (boundedAboveDerivedSingleFunctor.obj U)).complex ⟶
          cochainSingleZero U,
        DerivedCategory.Q.map ε =
          (boundedAboveDerivedChosenModel (boundedAboveDerivedSingleFunctor.obj U)).iso.hom := by
    let A := boundedAboveDerivedChosenModel (boundedAboveDerivedSingleFunctor.obj U)
    let B := projectiveResolutionDerivedModel (projectiveResolution U)
    refine ⟨A.map B (𝟙 _) ≫ projectiveResolutionCochainAugmentation (projectiveResolution U), ?_⟩
    rw [Functor.map_comp]
    change DerivedCategory.Q.map (A.map B (𝟙 _)) ≫ B.iso.hom = A.iso.hom
    rw [A.map_naturality, Category.comp_id]
  obtain ⟨εP, hεP⟩ := aug M
  obtain ⟨εQ, hεQ⟩ := aug N
  let PM := boundedAboveDerivedBaseChangeSingleModel φ M hM
  let PN := boundedAboveDerivedBaseChangeSingleModel φ N hN
  let εM : PM.complex ⟶ cochainSingleZero (F.obj M) :=
    (F.mapHomologicalComplex (.up ℤ)).map εP ≫
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M
  let εN : PN.complex ⟶ cochainSingleZero (F.obj N) :=
    (F.mapHomologicalComplex (.up ℤ)).map εQ ≫
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app N
  let βM : (boundedAboveDerivedBaseChange φ).obj XM ⟶
      boundedAboveDerivedSingleFunctor.obj (F.obj M) :=
    (boundedAboveDerivedBaseChangeModuleAugmentationIso φ M hM).hom
  let βN : (boundedAboveDerivedBaseChange φ).obj XN ⟶
      boundedAboveDerivedSingleFunctor.obj (F.obj N) :=
    (boundedAboveDerivedBaseChangeModuleAugmentationIso φ N hN).hom
  have hεM : DerivedCategory.Q.map εM = PM.iso.hom :=
    boundedAboveDerivedBaseChangeSingleModel_augmentation φ M hM εP hεP
  have hεN : DerivedCategory.Q.map εN = PN.iso.hom :=
    boundedAboveDerivedBaseChangeSingleModel_augmentation φ N hN εQ hεQ
  have hm : DerivedCategory.Q.map (𝟙 (baseChange φ P.complex)) ≫ PM.iso.hom =
      (boundedAboveDerivedBaseChangeModel φ XM).iso.hom ≫ βM.hom := by
    change DerivedCategory.Q.map (𝟙 _) ≫ (𝟙 _ ≫ βM.hom) = 𝟙 _ ≫ βM.hom
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
  have hn : DerivedCategory.Q.map (𝟙 (baseChange φ Q.complex)) ≫ PN.iso.hom =
      (boundedAboveDerivedBaseChangeModel φ XN).iso.hom ≫ βN.hom := by
    change DerivedCategory.Q.map (𝟙 _) ≫ (𝟙 _ ≫ βN.hom) = 𝟙 _ ≫ βN.hom
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
  have ht := boundedAboveDerivedTensorModelIso_naturality
    (boundedAboveDerivedBaseChangeModel φ XM) PM
    (boundedAboveDerivedBaseChangeModel φ XN) PN βM βN (𝟙 _) (𝟙 _) hm hn
  rw [cochainTensorMap_id, CategoryTheory.Functor.map_id, Category.comp_id] at ht
  have haugS := boundedAboveDerivedTensorModuleAugmentation_projective_models
    PM PN εM εN hεM hεN
  let σ : baseChange φ (boundedAboveDerivedTensorModel XM XN).complex ⟶
      cochainTensor PM.complex PN.complex :=
    (cochainTensorBaseChangeIso φ P.complex Q.complex).hom
  have hleft :
      (boundedAboveDerivedTensorBaseChangeModuleIso φ M N hM hN).hom.hom ≫
          (boundedAboveDerivedTensorModuleAugmentation (F.obj M)).app (F.obj N) =
        (boundedAboveDerivedBaseChangeModelIso φ (boundedAboveDerivedTensor.obj (XM, XN))
          (boundedAboveDerivedTensorModel XM XN)).hom ≫
        DerivedCategory.Q.map
          (σ ≫ cochainTensorMap εM εN ≫ (cochainSingleTensorIso (F.obj M) (F.obj N)).hom) := by
    rw [haugS]
    change ((boundedAboveDerivedTensorBaseChangeIso φ XM XN).hom.hom ≫
        (boundedAboveDerivedTensor.map (βM, βN)).hom) ≫
        ((boundedAboveDerivedTensorModelIso _ _ PM PN).hom ≫ _) = _
    have hstep := congrArg (fun t =>
      (boundedAboveDerivedTensorBaseChangeIso φ XM XN).hom.hom ≫ t ≫
        DerivedCategory.Q.map
          (cochainTensorMap εM εN ≫ (cochainSingleTensorIso (F.obj M) (F.obj N)).hom)) ht
    simp only [Category.assoc] at hstep
    calc
      _ = (boundedAboveDerivedTensorBaseChangeIso φ XM XN).hom.hom ≫
          (boundedAboveDerivedTensorModelIso _ _
            (boundedAboveDerivedBaseChangeModel φ XM)
            (boundedAboveDerivedBaseChangeModel φ XN)).hom ≫
          DerivedCategory.Q.map
            (cochainTensorMap εM εN ≫ (cochainSingleTensorIso (F.obj M) (F.obj N)).hom) := by
        simpa only [Category.assoc] using hstep
      _ = _ := by
        simp only [σ, boundedAboveDerivedTensorBaseChangeIso, ObjectProperty.isoMk,
          ObjectProperty.homMk_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
          Category.assoc, Iso.inv_hom_id_assoc]
        simp only [Functor.map_comp]
        rfl
  have haugR := boundedAboveDerivedTensorModuleAugmentation_projective_models
    P Q εP εQ hεP hεQ
  rw [boundedAboveDerivedTensorModelIso_chosen_hom, Category.id_comp] at haugR
  let g : boundedAboveDerivedTensor.obj (XM, XN) ⟶
      boundedAboveDerivedSingleFunctor.obj (M ⊗ N) :=
    ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation M).app N)
  have hraw : DerivedCategory.Q.map
      (cochainTensorMap εP εQ ≫ (cochainSingleTensorIso M N).hom) =
      (boundedAboveDerivedTensorModel XM XN).iso.hom ≫ g.hom := by
    change _ = 𝟙 _ ≫ (boundedAboveDerivedTensorModuleAugmentation M).app N
    rw [Category.id_comp]
    exact haugR.symm
  have hright := boundedAboveDerivedBaseChangeModuleAugmentation_map_model φ
    (boundedAboveDerivedTensor.obj (XM, XN)) (boundedAboveDerivedTensorModel XM XN)
    (M ⊗ N) g (cochainTensorMap εP εQ ≫ (cochainSingleTensorIso M N).hom) hraw
  rw [hleft]
  change _ = ((boundedAboveDerivedBaseChange φ).map g).hom ≫
    (boundedAboveDerivedBaseChangeModuleAugmentation φ).app (M ⊗ N) ≫
    DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat S) 0).map
      (Functor.OplaxMonoidal.δ F M N))
  rw [← Category.assoc ((boundedAboveDerivedBaseChange φ).map g).hom
      ((boundedAboveDerivedBaseChangeModuleAugmentation φ).app (M ⊗ N)),
    hright, Category.assoc, ← Functor.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  exact (cochainTensorBaseChangeIso_augmentation φ εP εQ).symm

end SerrePositivity
