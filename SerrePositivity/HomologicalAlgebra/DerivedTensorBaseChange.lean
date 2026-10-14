module

public import SerrePositivity.HomologicalAlgebra.DerivedTensorRealization
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # 加群の実導来係数変更

環準同型に沿う係数拡大の左導来関手を、係数変更先の標準導来圏に実現する。
係数環の平坦性は仮定しない。一般複体の導来テンソルとその結合・底変換比較は
この加群の入口とは別に構成する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity
attribute [local instance] HasDerivedCategory.standard
variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)

/-- 係数拡大を係数制限して得る通常テンソルの標準比較。 -/
def extendRestrictTensorIso :
    ModuleCat.extendScalars.{u, u, u} φ ⋙ ModuleCat.restrictScalars φ ≅
      (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) (fun f ↦ ?_)
  · refine (show ((ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj M)) ≃ₗ[R]
        ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))).obj M from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := ?_ }).toModuleIso
    intro r x
    rfl
  · ext x
    rfl

/-- 完全な係数制限関手は鎖複体のホモロジーと可換。 -/
def restrictChainHomologyIso (n : ℕ) :
    (ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (.down ℕ) ⋙
      HomologicalComplex.homologyFunctor _ _ n ≅
      HomologicalComplex.homologyFunctor _ _ n ⋙ ModuleCat.restrictScalars φ :=
  NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso (ModuleCat.restrictScalars φ))
    (fun f ↦ CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ n).map f) (ModuleCat.restrictScalars φ))

/-- ホモトピー圏上でも係数制限とホモロジーの比較は自然。 -/
def restrictHomotopyChainHomologyIso (n : ℕ) :
    (ModuleCat.restrictScalars.{u} φ).mapHomotopyCategory (.down ℕ) ⋙
      HomotopyCategory.homologyFunctor _ _ n ≅
      HomotopyCategory.homologyFunctor _ _ n ⋙ ModuleCat.restrictScalars φ :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((ModuleCat.restrictScalars.{u} φ).mapHomotopyCategoryFactors _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (HomotopyCategory.homologyFunctorFactors _ _ _) ≪≫
      restrictChainHomologyIso φ n ≪≫
      Functor.isoWhiskerRight (HomotopyCategory.homologyFunctorFactors _ _ _).symm _ ≪≫
      Functor.associator _ _ _)

/-- 係数拡大の分解モデルを係数制限すると、既存の導来テンソルのモデルを得る。 -/
def restrictDerivedBaseChangeHomotopyIso :
    (ModuleCat.extendScalars.{u, u, u} φ).leftDerivedToHomotopyCategory ⋙
      (ModuleCat.restrictScalars.{u} φ).mapHomotopyCategory (.down ℕ) ≅
      ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))).leftDerivedToHomotopyCategory :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapHomotopyCategoryCompIso (extendRestrictTensorIso φ) _)

/-- 環準同型に沿う実導来係数変更。値は変更先の環上の実導来圏。 -/
def derivedModuleBaseChange : ModuleCat.{u} R ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (ModuleCat.extendScalars.{u, u, u} φ).leftDerivedToHomotopyCategory ⋙
    chainDerivedRealization A

/-- 導来係数変更のH⁻ⁿは係数拡大の第n左導来関手。 -/
def derivedModuleBaseChangeHomologyIso (n : ℕ) :
    derivedModuleBaseChange φ ⋙ DerivedCategory.homologyFunctor _ (-(n : ℤ)) ≅
      (ModuleCat.extendScalars.{u, u, u} φ).leftDerived n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (chainDerivedRealizationHomologyIso A n)

/-- 導来係数変更のホモロジーは係数制限後に既存のTorと自然に一致する。
変更先の環の作用を保持した比較であり、係数環の平坦性を仮定しない。 -/
def derivedModuleBaseChangeTorIso (n : ℕ) :
    (derivedModuleBaseChange φ ⋙ DerivedCategory.homologyFunctor _ (-(n : ℤ))) ⋙
      ModuleCat.restrictScalars φ ≅
      (Tor (ModuleCat.{u} R) n).obj ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) :=
  Functor.isoWhiskerRight (derivedModuleBaseChangeHomologyIso φ n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictHomotopyChainHomologyIso φ n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictDerivedBaseChangeHomotopyIso φ) _

/-- 係数制限は零性を反映するため、上の比較はTor消滅も反映する。 -/
theorem derivedModuleBaseChange_negative_homology_vanishes_iff (M : ModuleCat.{u} R) :
    (∀ n : ℕ, 0 < n → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A)
      (-(n : ℤ))).obj ((derivedModuleBaseChange φ).obj M))) ↔
    ∀ n : ℕ, 0 < n → IsZero
      (((Tor (ModuleCat.{u} R) n).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))).obj M) := by
  refine forall₂_congr fun n _ ↦ ?_
  have he : IsZero ((ModuleCat.restrictScalars φ).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
        ((derivedModuleBaseChange φ).obj M))) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
        ((derivedModuleBaseChange φ).obj M)) := by
    simp only [ModuleCat.isZero_iff_subsingleton]
    rfl
  exact he.symm.trans ((derivedModuleBaseChangeTorIso φ n).app M).isZero_iff

/-- 零次では通常の係数拡大と自然に一致する。 -/
def derivedModuleBaseChangeH0Iso :
    derivedModuleBaseChange φ ⋙ DerivedCategory.homologyFunctor _ 0 ≅
      ModuleCat.extendScalars.{u, u, u} φ :=
  derivedModuleBaseChangeHomologyIso φ 0 ≪≫
    (ModuleCat.extendScalars.{u, u, u} φ).leftDerivedZeroIsoSelf

/-- 通常の係数拡大を零次数に置いた対象への標準augmentation。 -/
def derivedModuleBaseChangeAugmentation : derivedModuleBaseChange φ ⟶
    ModuleCat.extendScalars.{u, u, u} φ ⋙ DerivedCategory.singleFunctor _ 0 :=
  Functor.whiskerLeft _ (chainDerivedAugmentation A) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (ModuleCat.extendScalars.{u, u, u} φ).leftDerivedZeroIsoSelf.hom _

/-- 標準augmentationがH⁰に誘導する射は上の自然比較である。 -/
theorem derivedModuleBaseChangeAugmentation_homology (M : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor _ 0).map
        ((derivedModuleBaseChangeAugmentation φ).app M) ≫
      (realizedSingleH0Iso A).hom.app ((ModuleCat.extendScalars φ).obj M) =
      (derivedModuleBaseChangeH0Iso φ).hom.app M := by
  have hn := (realizedSingleH0Iso A).hom.naturality
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerivedZeroIsoSelf.hom.app M)
  simp only [Functor.comp_map, Functor.id_map] at hn
  change (DerivedCategory.homologyFunctor _ 0).map
    ((chainDerivedAugmentation A).app _ ≫ (DerivedCategory.singleFunctor _ 0).map
      ((ModuleCat.extendScalars.{u, u, u} φ).leftDerivedZeroIsoSelf.hom.app M)) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc]
  erw [chainDerivedAugmentation_homology]
  rfl

/-- 任意の射影分解に係数拡大を施した複体で実導来係数変更を計算する。 -/
def derivedModuleBaseChangeResolutionIso {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (derivedModuleBaseChange φ).obj M ≅ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (.down ℕ)).obj
        P.complex |>.extend embUp) :=
  (chainDerivedRealization A).mapIso
    (P.isoLeftDerivedToHomotopyCategoryObj (ModuleCat.extendScalars.{u, u, u} φ)) ≪≫
    (chainDerivedRealizationComplexNatIso A).app _

/-- 任意の射影分解による計算は、加群写像の標準持ち上げと両立する。 -/
@[reassoc] theorem derivedModuleBaseChangeResolutionIso_naturality
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (derivedModuleBaseChange φ).map f ≫ (derivedModuleBaseChangeResolutionIso φ Q).hom =
      (derivedModuleBaseChangeResolutionIso φ P).hom ≫ DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (.down ℕ)).map
            (ProjectiveResolution.lift f P Q)) embUp) := by
  have hp := ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality
    f P Q (ProjectiveResolution.lift f P Q) (by simp) (ModuleCat.extendScalars.{u, u, u} φ)
  have hn := (chainDerivedRealizationComplexNatIso A).hom.naturality
    (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (.down ℕ)).map
      (ProjectiveResolution.lift f P Q))
  simp only [Functor.comp_map] at hn
  change (chainDerivedRealization A).map _ ≫ (chainDerivedRealization A).map _ ≫ _ = _
  rw [← Functor.map_comp_assoc, hp, Functor.map_comp, Category.assoc]
  simpa only [derivedModuleBaseChangeResolutionIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.comp_map, ComplexShape.Embedding.extendFunctor_map,
    Category.assoc] using congrArg (fun g ↦ (chainDerivedRealization A).map
      (P.isoLeftDerivedToHomotopyCategoryObj (ModuleCat.extendScalars φ)).hom ≫ g) hn

/-- 導来係数変更は正の余鎖次数にホモロジーを持たない。 -/
theorem derivedModuleBaseChange_homology_isZero_positive (M : ModuleCat.{u} R)
    (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj ((derivedModuleBaseChange φ).obj M)) :=
  chainDerivedRealization_homology_isZero_positive A _ i hi

end SerrePositivity
