module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelHomotopy
public import SerrePositivity.DifferentialGraded.Morita.KernelAugmentation
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionNaturality

/-! # kernel係数変更を導来作用へ接続するH⁰増大比較

比較射の存在と可逆性を分ける。可逆性のモデル条件は明示して受け取る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 導来係数変更から通常係数変更への比較を、全H⁰入力射へ降ろす。 -/
def scalarExtensionHomotopyAugmentation :
    moduleHomotopyToDerivedClosed A D ⋙ derivedExtension φ D ⟶
      moduleExtensionHomotopyToDerived φ D :=
  Quotient.natTransLift (boundaryRelation A (RightModule A D))
    (Functor.whiskerRight (moduleToHomotopyDerivedIso A D).hom (derivedExtension φ D) ≫
      derivedExtensionAugmentation φ D ≫
        eqToHom (moduleExtensionHomotopyToDerived_fac φ D).symm)

lemma scalarExtensionHomotopyAugmentation_app (M : ModuleCategory A D) :
    (scalarExtensionHomotopyAugmentation φ D).app ((moduleToHomotopy A D).obj M) =
      (derivedExtension φ D).map ((moduleToHomotopyDerivedIso A D).hom.app M) ≫
        (derivedExtensionAugmentation φ D).app M := by
  simp only [scalarExtensionHomotopyAugmentation, Quotient.natTransLift_app,
    NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_refl, Category.comp_id]

lemma scalarExtensionHomotopyAugmentation_isIso (M : ModuleCategory A D)
    (hM : IsIso ((derivedExtensionAugmentation φ D).app M)) :
    IsIso ((scalarExtensionHomotopyAugmentation φ D).app ((moduleToHomotopy A D).obj M)) := by
  let := hM
  rw [scalarExtensionHomotopyAugmentation_app]
  infer_instance

variable (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 主導来kernel作用から通常作用への増大を全H⁰入力射へ降ろす。 -/
def scalarKernelHomotopyAugmentation :
    moduleHomotopyToDerivedClosed A D ⋙ kernelDerivedTensorOnBimodule A D E P ⟶
      kernelHomotopyToDerived A D E P :=
  Quotient.natTransLift (boundaryRelation A (RightModule A D))
    (Functor.whiskerRight (moduleToHomotopyDerivedIso A D).hom
        (kernelDerivedTensorOnBimodule A D E P) ≫
      kernelDerivedTensorAugmentation A D E P ≫
        (kernelTensorHomotopyComputationIso A D E P).inv)

lemma scalarKernelHomotopyAugmentation_app (M : ModuleCategory A D) :
    (scalarKernelHomotopyAugmentation D E P).app ((moduleToHomotopy A D).obj M) =
      (kernelDerivedTensorOnBimodule A D E P).map ((moduleToHomotopyDerivedIso A D).hom.app M) ≫
        (kernelDerivedTensorAugmentation A D E P).app M ≫
          (kernelTensorHomotopyComputationIso A D E P).inv.app M := by
  simp only [scalarKernelHomotopyAugmentation, Quotient.natTransLift_app,
    NatTrans.comp_app, Functor.whiskerRight_app]

lemma scalarKernelHomotopyAugmentation_isIso (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    IsIso ((scalarKernelHomotopyAugmentation D E P).app ((moduleToHomotopy A D).obj M)) := by
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P M hM
  rw [scalarKernelHomotopyAugmentation_app]
  infer_instance

/-- 係数変更前後の二つの導来作用を比較する共通の計算モデル。 -/
def scalarKernelDerivedBaseChangeModel :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A' (DGBaseChange φ E) :=
  moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D) ⋙
    scalarModuleExtensionHomotopy φ D ⋙
      kernelHomotopyToDerived A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)

/-- 出力の導来係数変更から共通モデルへの自然な比較。 -/
def scalarKernelDerivedBaseChangeLeft :
    kernelDerivedTensorOnBimodule A D E P ⋙ derivedExtension φ E ⟶
      scalarKernelDerivedBaseChangeModel φ D E P :=
  Functor.whiskerLeft
      (moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D) ⋙
        (kernelTensor A D E P).onHomotopy) (scalarExtensionHomotopyAugmentation φ E) ≫
    (Functor.isoWhiskerLeft
      (moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D))
      (scalarKernelBalancedHomotopyDerivedIso φ D E P)).hom

/-- 入力の導来係数変更後のkernel作用から共通モデルへの自然な比較。 -/
def scalarKernelDerivedBaseChangeRight :
    derivedExtension φ D ⋙
        kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P) ⟶
      scalarKernelDerivedBaseChangeModel φ D E P :=
  Functor.whiskerLeft
    (moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D))
    (Functor.whiskerRight (scalarExtensionHomotopyDerivedIso φ D).inv
        (kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)) ≫
      Functor.whiskerLeft (scalarModuleExtensionHomotopy φ D)
        (scalarKernelHomotopyAugmentation (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)))

lemma scalarKernelDerivedBaseChangeLeft_isIso
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj))) :
    IsIso (scalarKernelDerivedBaseChangeLeft φ D E P) := by
  have hb (M : ModuleCategory A D) :
      IsIso ((scalarKernelDerivedBaseChangeLeft φ D E P).app ((moduleToDerived A D).obj M)) := by
    let R := moduleCanonicalProjectiveResolution A D M
    let τ := scalarExtensionHomotopyAugmentation φ E
    let Z := (kernelTensor A D E P).onHomotopy
    let eOut := Z.mapIso (moduleDerivedResolutionComputation A D
        (moduleCanonicalProjectiveResolution A D) M) ≪≫
      (eqToIso (kernelTensor A D E P).onHomotopy_fac).app R.obj
    have hmid : IsIso (τ.app
        (((kernelTensor A D E P).onClosed ⋙ moduleToHomotopy A E).obj R.obj)) :=
      scalarExtensionHomotopyAugmentation_isIso φ E
        ((kernelTensor A D E P).onClosed.obj R.obj) (hAug M)
    have hi : IsIso (τ.app (Z.obj
        ((moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D)).obj
          ((moduleToDerived A D).obj M)))) := by
      rw [← τ.naturality_2 eOut]
      infer_instance
    let := hi
    change IsIso (τ.app _ ≫
      (scalarKernelBalancedHomotopyDerivedIso φ D E P).hom.app
        ((moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D)).obj
          ((moduleToDerived A D).obj M)))
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let M := (moduleToDerived A D).objPreimage X
  let e := (moduleToDerived A D).objObjPreimageIso X
  have := hb M
  rw [← (scalarKernelDerivedBaseChangeLeft φ D E P).naturality_1 e]
  infer_instance

lemma scalarKernelDerivedBaseChangeRight_isIso
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    IsIso (scalarKernelDerivedBaseChangeRight φ D E P) := by
  have hb (M : ModuleCategory A D) :
      IsIso ((scalarKernelDerivedBaseChangeRight φ D E P).app ((moduleToDerived A D).obj M)) := by
    let R := moduleCanonicalProjectiveResolution A D M
    let H := scalarModuleExtensionHomotopy φ D
    let τ := scalarKernelHomotopyAugmentation (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P)
    let eIn := H.mapIso (moduleDerivedResolutionComputation A D
        (moduleCanonicalProjectiveResolution A D) M) ≪≫
      (eqToIso (scalarModuleExtensionHomotopy_fac φ D)).app R.obj
    have hmid : IsIso (τ.app
        ((moduleExtension φ D ⋙ moduleToHomotopy A' (DGBaseChange φ D)).obj R.obj)) :=
      scalarKernelHomotopyAugmentation_isIso (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P) ((moduleExtension φ D).obj R.obj) (hP' M)
    have hi : IsIso (τ.app (H.obj
        ((moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D)).obj
          ((moduleToDerived A D).obj M)))) := by
      rw [← τ.naturality_2 eIn]
      infer_instance
    let := hi
    change IsIso ((kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P)).map
        ((scalarExtensionHomotopyDerivedIso φ D).inv.app _) ≫ τ.app _)
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let M := (moduleToDerived A D).objPreimage X
  let e := (moduleToDerived A D).objObjPreimageIso X
  have := hb M
  rw [← (scalarKernelDerivedBaseChangeRight φ D E P).naturality_1 e]
  infer_instance

/-- モデルの可逆性を明示した、全主導来入力射に自然なdg加群値の係数変更比較。 -/
def scalarKernelDerivedBaseChangeIso
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    kernelDerivedTensorOnBimodule A D E P ⋙ derivedExtension φ E ≅
      derivedExtension φ D ⋙
        kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P) := by
  have := scalarKernelDerivedBaseChangeLeft_isIso φ D E P hAug
  have := scalarKernelDerivedBaseChangeRight_isIso φ D E P hP'
  exact asIso (scalarKernelDerivedBaseChangeLeft φ D E P) ≪≫
    (asIso (scalarKernelDerivedBaseChangeRight φ D E P)).symm

lemma scalarKernelDerivedBaseChangeIso_hom_comp_right
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    (scalarKernelDerivedBaseChangeIso φ D E P hAug hP').hom ≫
        scalarKernelDerivedBaseChangeRight φ D E P =
      scalarKernelDerivedBaseChangeLeft φ D E P := by
  have := scalarKernelDerivedBaseChangeLeft_isIso φ D E P hAug
  have := scalarKernelDerivedBaseChangeRight_isIso φ D E P hP'
  simp only [scalarKernelDerivedBaseChangeIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- 出力圏の局所Hom条件とhPNから、出力の通常モデルでの係数変更計算を保証する。 -/
lemma scalarKernelOutputAugmentation_isIso
    (hE : localHomKFlat A E)
    (hPN : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        (P.leftAt e))) (M : ModuleCategory A D) :
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)) := by
  apply derivedExtensionAugmentation_isIso_of_objectwiseKFlat φ E _ hE
  intro e
  exact hPN M e

/-- hPN・hP'を保持した、出力dg加群全体の導来係数変更比較。
局所Hom条件hEは出力の増大比較を反転するためにのみ使う。 -/
def scalarKernelDerivedBaseChangeIso_ofKFlatModels
    (hE : localHomKFlat A E)
    (hPN : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        (P.leftAt e)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    kernelDerivedTensorOnBimodule A D E P ⋙ derivedExtension φ E ≅
      derivedExtension φ D ⋙
        kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P) :=
  scalarKernelDerivedBaseChangeIso φ D E P
    (scalarKernelOutputAugmentation_isIso φ D E P hE hPN) hP'

end SerrePositivity.DifferentialGraded.Morita
