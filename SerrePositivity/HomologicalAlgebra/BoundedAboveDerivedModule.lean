module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedTensorBaseChange
public import SerrePositivity.HomologicalAlgebra.MapExtend

/-! # Compatibility of complex derived base change with the existing module functor -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- A module as an object of the standard bounded-above derived category. -/
def boundedAboveDerivedSingleFunctor :
    ModuleCat.{u} R ⥤ DerivedCategory.Minus (ModuleCat.{u} R) where
  obj M := ⟨(DerivedCategory.singleFunctor (ModuleCat R) 0).obj M, ⟨0, inferInstance⟩⟩
  map f := ObjectProperty.homMk ((DerivedCategory.singleFunctor (ModuleCat R) 0).map f)
  map_id M := by
    apply InducedCategory.hom_ext
    change (DerivedCategory.singleFunctor (ModuleCat R) 0).map (𝟙 M) = _
    exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by
    apply InducedCategory.hom_ext
    change (DerivedCategory.singleFunctor (ModuleCat R) 0).map (f ≫ g) = _
    exact CategoryTheory.Functor.map_comp _ _ _

/-- Augmentation of an arbitrary module projective resolution after integer reindexing. -/
def projectiveResolutionCochainAugmentation {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    extRes P ⟶ (CochainComplex.singleFunctor (ModuleCat R) 0).obj M :=
  HomologicalComplex.extendMap P.π embUp ≫
    (HomologicalComplex.extendSingleIso embUp M 0 0 embUp_f_zero).hom

instance projectiveResolutionCochainAugmentation_quasiIso
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    QuasiIso (projectiveResolutionCochainAugmentation P) := by
  dsimp [projectiveResolutionCochainAugmentation]
  infer_instance

lemma projectiveResolutionCochainAugmentation_naturality
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    extLift P f Q ≫ projectiveResolutionCochainAugmentation Q =
      projectiveResolutionCochainAugmentation P ≫
        (CochainComplex.singleFunctor (ModuleCat R) 0).map f := by
  dsimp only [projectiveResolutionCochainAugmentation, extLift]
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    ProjectiveResolution.lift_commutes, HomologicalComplex.extendMap_comp, Category.assoc]
  exact congrArg (fun t => HomologicalComplex.extendMap P.π embUp ≫ t)
    ((extendChainSingleNatIso R).hom.naturality f)

/-- Any module projective resolution supplies a model of the actual single derived object. -/
def projectiveResolutionDerivedModel {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    BoundedAboveDerivedModel ((boundedAboveDerivedSingleFunctor (R := R)).obj M).obj where
  complex := extRes P
  bound := 0
  bounded := (CochainComplex.isStrictlyLE_iff _ _).mpr (extRes_isZero_X P)
  projective := extRes_projective P
  iso := asIso (DerivedCategory.Q.map (projectiveResolutionCochainAugmentation P))

/-- The complex-level derived scalar extension recovers the existing module-level construction. -/
def boundedAboveDerivedBaseChangeModuleIso (φ : R →+* S) (M : ModuleCat.{u} R) :
    ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj M)).obj ≅
      (derivedModuleBaseChange φ).obj M :=
  boundedAboveDerivedBaseChangeModelIso φ _
    (projectiveResolutionDerivedModel (projectiveResolution M)) ≪≫
    DerivedCategory.Q.mapIso (mapExtendIso (ModuleCat.extendScalars φ)
      (projectiveResolution M).complex embUp) ≪≫
    (derivedModuleBaseChangeResolutionIso φ (projectiveResolution M)).symm

lemma boundedAboveDerivedBaseChangeModuleIso_naturality (φ : R →+* S)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((boundedAboveDerivedBaseChange φ).map (boundedAboveDerivedSingleFunctor.map f)).hom ≫
        (boundedAboveDerivedBaseChangeModuleIso φ N).hom =
      (boundedAboveDerivedBaseChangeModuleIso φ M).hom ≫ (derivedModuleBaseChange φ).map f := by
  let P := projectiveResolution M
  let Q := projectiveResolution N
  let F := ModuleCat.extendScalars φ
  have hp : DerivedCategory.Q.map (extLift P f Q) ≫ (projectiveResolutionDerivedModel Q).iso.hom =
      (projectiveResolutionDerivedModel P).iso.hom ≫
        (boundedAboveDerivedSingleFunctor.map f).hom := by
    change DerivedCategory.Q.map (extLift P f Q) ≫
        DerivedCategory.Q.map (projectiveResolutionCochainAugmentation Q) =
      DerivedCategory.Q.map (projectiveResolutionCochainAugmentation P) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat R) 0).map f)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      projectiveResolutionCochainAugmentation_naturality]
  have hl := boundedAboveLeftDerivedModelIso_naturality F
    (projectiveResolutionDerivedModel P) (projectiveResolutionDerivedModel Q)
    (boundedAboveDerivedSingleFunctor.map f) (extLift P f Q) hp
  have hr := derivedModuleBaseChangeResolutionIso_naturality φ f P Q
  apply (cancel_mono (derivedModuleBaseChangeResolutionIso φ Q).hom).mp
  simp only [Q, boundedAboveDerivedBaseChangeModuleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hr]
  simp only [P, Q, Iso.inv_hom_id_assoc]
  erw [← Category.assoc, hl, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (mapExtendIso_naturality F embUp
    (ProjectiveResolution.lift f P Q))

/-- The complex and module versions agree as functors, not just objectwise. -/
def boundedAboveDerivedBaseChangeModuleNatIso (φ : R →+* S) :
    boundedAboveDerivedSingleFunctor ⋙ boundedAboveDerivedBaseChange φ ⋙
        DerivedCategory.Minus.ι ≅ derivedModuleBaseChange φ :=
  NatIso.ofComponents (boundedAboveDerivedBaseChangeModuleIso φ)
    (fun f => boundedAboveDerivedBaseChangeModuleIso_naturality φ f)

/-- The complex construction has the existing natural H0 comparison on modules. -/
def boundedAboveDerivedBaseChangeModuleH0Iso (φ : R →+* S) :
    (boundedAboveDerivedSingleFunctor ⋙ boundedAboveDerivedBaseChange φ ⋙
      DerivedCategory.Minus.ι) ⋙ DerivedCategory.homologyFunctor (ModuleCat S) 0 ≅
      ModuleCat.extendScalars φ :=
  Functor.isoWhiskerRight (boundedAboveDerivedBaseChangeModuleNatIso φ) _ ≪≫
    derivedModuleBaseChangeH0Iso φ

/-- In all negative degrees the new construction naturally recovers the existing Tor functors. -/
def boundedAboveDerivedBaseChangeModuleTorIso (φ : R →+* S) (n : ℕ) :
    (((boundedAboveDerivedSingleFunctor ⋙ boundedAboveDerivedBaseChange φ ⋙
      DerivedCategory.Minus.ι) ⋙ DerivedCategory.homologyFunctor (ModuleCat S) (-(n : ℤ))) ⋙
      ModuleCat.restrictScalars φ) ≅
      (Tor (ModuleCat.{u} R) n).obj ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (boundedAboveDerivedBaseChangeModuleNatIso φ) _) _ ≪≫
      derivedModuleBaseChangeTorIso φ n

/-- Transport the established standard module augmentation through the proved natural comparison. -/
def boundedAboveDerivedBaseChangeModuleAugmentation (φ : R →+* S) :
    boundedAboveDerivedSingleFunctor ⋙ boundedAboveDerivedBaseChange φ ⋙
        DerivedCategory.Minus.ι ⟶
      ModuleCat.extendScalars φ ⋙ DerivedCategory.singleFunctor (ModuleCat S) 0 :=
  (boundedAboveDerivedBaseChangeModuleNatIso φ).hom ≫ derivedModuleBaseChangeAugmentation φ

/-- On H0 the transported standard augmentation induces precisely the ordinary scalar extension. -/
lemma boundedAboveDerivedBaseChangeModuleAugmentation_homology (φ : R →+* S)
    (M : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat S) 0).map
        ((boundedAboveDerivedBaseChangeModuleAugmentation φ).app M) ≫
      (realizedSingleH0Iso S).hom.app ((ModuleCat.extendScalars φ).obj M) =
        (boundedAboveDerivedBaseChangeModuleH0Iso φ).hom.app M := by
  change (DerivedCategory.homologyFunctor (ModuleCat S) 0).map
    ((boundedAboveDerivedBaseChangeModuleNatIso φ).hom.app M ≫
      (derivedModuleBaseChangeAugmentation φ).app M) ≫ _ = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc, derivedModuleBaseChangeAugmentation_homology]
  rfl

end SerrePositivity
