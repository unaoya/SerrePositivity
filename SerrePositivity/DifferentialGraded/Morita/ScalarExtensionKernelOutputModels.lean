module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelHomotopyNaturality
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelDerivedComparison

/-! # 出力係数変更の通常モデル上の比較射計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

lemma scalarOutputHomotopyDerivedIso_inv_app (N : ModuleCategory A E) :
    (scalarExtensionHomotopyDerivedIso φ E).inv.app ((moduleToHomotopy A E).obj N) =
      ((moduleToHomotopyDerivedIso A' (DGBaseChange φ E)).app
        ((moduleExtension φ E).obj N)).inv := by
  simp only [scalarExtensionHomotopyDerivedIso, Quotient.natIsoLift_inv,
    Quotient.natTransLift_app, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, eqToIso.hom, eqToIso.inv, eqToHom_app]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  change ((moduleToHomotopyDerivedIso A' (DGBaseChange φ E)).app
    ((moduleExtension φ E).obj N)).inv ≫ 𝟙 _ = _
  exact Category.comp_id _

lemma scalarKernelOutputHomotopyComputation_hom (M : ModuleCategory A D) :
    (kernelTensorHomotopyComputation A D E P M).hom =
      ((moduleToHomotopyDerivedIso A E).app ((kernelTensor A D E P).onClosed.obj M)).hom := by
  change (moduleHomotopyToDerivedClosed A E).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

lemma scalarKernelOutputLeft_closed (M : ModuleCategory A D) :
    (derivedExtension φ E).map (kernelTensorHomotopyComputation A D E P M).hom ≫
        (derivedExtensionAugmentation φ E).app ((kernelTensor A D E P).onClosed.obj M) ≫
        (moduleToDerived A' (DGBaseChange φ E)).map
          (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M)).hom =
      (scalarExtensionHomotopyAugmentation φ E).app
          ((kernelTensor A D E P).onHomotopy.obj ((moduleToHomotopy A D).obj M)) ≫
        (scalarKernelBalancedHomotopyDerivedIso φ D E P).hom.app ((moduleToHomotopy A D).obj M) ≫
        (kernelTensorHomotopyComputation A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P) ((moduleExtension φ D).obj M)).hom := by
  change _ = (scalarExtensionHomotopyAugmentation φ E).app
    ((moduleToHomotopy A E).obj ((kernelTensor A D E P).onClosed.obj M)) ≫ _
  rw [scalarExtensionHomotopyAugmentation_app]
  rw [scalarKernelOutputHomotopyComputation_hom]
  simp only [scalarKernelBalancedHomotopyDerivedIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    scalarKernelBalancedHomotopyIso_app, Category.assoc]
  change _ = _ ≫ _ ≫
    (scalarExtensionHomotopyDerivedIso φ E).inv.app
      ((moduleToHomotopy A E).obj ((kernelTensor A D E P).onClosed.obj M)) ≫ _
  rw [scalarOutputHomotopyDerivedIso_inv_app, scalarKernelOutputHomotopyComputation_hom]
  have hn := (moduleToHomotopyDerivedIso A' (DGBaseChange φ E)).hom.naturality
    (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M)).hom
  simp only [Functor.comp_map] at hn
  erw [hn]
  change _ = _ ≫ _ ≫
    ((moduleToHomotopyDerivedIso A' (DGBaseChange φ E)).app
      ((moduleExtension φ E).obj ((kernelTensor A D E P).onClosed.obj M))).inv ≫
    ((moduleToHomotopyDerivedIso A' (DGBaseChange φ E)).app
      ((moduleExtension φ E).obj ((kernelTensor A D E P).onClosed.obj M))).hom ≫ _
  rw [Iso.inv_hom_id_assoc]
  rfl

/-- 係数変更正方形の共通モデルを、指定標準右解像度で計算する。 -/
def scalarKernelOutputModelComputation (M : ModuleCategory A D) :
    (scalarKernelDerivedBaseChangeModel φ D E P).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A' (DGBaseChange φ E)).obj
        ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).onClosed.obj
          ((moduleExtension φ D).obj (moduleCanonicalProjectiveResolution A D M).obj)) :=
  (scalarModuleExtensionHomotopy φ D ⋙
    kernelHomotopyToDerived A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P)).mapIso
      (moduleDerivedResolutionComputation A D (moduleCanonicalProjectiveResolution A D) M) ≪≫
    kernelTensorHomotopyComputation A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P)
      ((moduleExtension φ D).obj (moduleCanonicalProjectiveResolution A D M).obj)

/-- 出力増大経路を、標準モデル上の実際のbalanced比較へ計算する。 -/
lemma scalarKernelOutputLeft_model (M : ModuleCategory A D) :
    (scalarKernelDerivedBaseChangeLeft φ D E P).app ((moduleToDerived A D).obj M) ≫
        (scalarKernelOutputModelComputation φ D E P M).hom =
      (derivedExtension φ E).map
          (kernelResolutionDerivedTensorComputation A D E P
            (moduleCanonicalProjectiveResolution A D) M).hom ≫
        (derivedExtensionAugmentation φ E).app
          ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj) ≫
        (moduleToDerived A' (DGBaseChange φ E)).map
          (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A)
            (moduleCanonicalProjectiveResolution A D M).obj)).hom := by
  let δ := Functor.whiskerLeft (kernelTensor A D E P).onHomotopy
      (scalarExtensionHomotopyAugmentation φ E) ≫
    (scalarKernelBalancedHomotopyDerivedIso φ D E P).hom
  have hn := δ.naturality
    (moduleDerivedResolutionComputation A D (moduleCanonicalProjectiveResolution A D) M).hom
  simp only [Functor.comp_map] at hn
  simp only [scalarKernelDerivedBaseChangeLeft, scalarKernelOutputModelComputation,
    Iso.trans_hom, Functor.mapIso_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  change (δ.app _) ≫ _ ≫ _ = _
  rw [← Category.assoc]
  erw [← hn]
  rw [Category.assoc]
  simp only [δ, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  erw [← scalarKernelOutputLeft_closed φ D E P (moduleCanonicalProjectiveResolution A D M).obj]
  simp only [kernelResolutionDerivedTensorComputation, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- 入力係数変更後の増大経路は、通常入力で実際のkernel増大を計算する。 -/
lemma scalarKernelOutputRight_closed (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P)).map
          ((scalarExtensionHomotopyDerivedIso φ D).inv.app ((moduleToHomotopy A D).obj M)) ≫
        (scalarKernelHomotopyAugmentation (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).app
            ((scalarModuleExtensionHomotopy φ D).obj ((moduleToHomotopy A D).obj M)) ≫
        (kernelTensorHomotopyComputation A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P) ((moduleExtension φ D).obj M)).hom =
      (kernelDerivedTensorAugmentation A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P)).app ((moduleExtension φ D).obj M) := by
  rw [scalarOutputHomotopyDerivedIso_inv_app]
  change _ ≫ (scalarKernelHomotopyAugmentation (DGBaseChange φ D) (DGBaseChange φ E)
    (scalarKernel φ D E P)).app
      ((moduleToHomotopy A' (DGBaseChange φ D)).obj ((moduleExtension φ D).obj M)) ≫ _ = _
  rw [scalarKernelHomotopyAugmentation_app]
  simp only [Category.assoc]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  change (kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
    (scalarKernel φ D E P)).map
      (((moduleToHomotopyDerivedIso A' (DGBaseChange φ D)).app
        ((moduleExtension φ D).obj M)).inv ≫
       ((moduleToHomotopyDerivedIso A' (DGBaseChange φ D)).app
        ((moduleExtension φ D).obj M)).hom) ≫ _ = _
  rw [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  change _ ≫ (kernelTensorHomotopyComputation A' (DGBaseChange φ D) (DGBaseChange φ E)
    (scalarKernel φ D E P) ((moduleExtension φ D).obj M)).inv ≫
    (kernelTensorHomotopyComputation A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P) ((moduleExtension φ D).obj M)).hom = _
  rw [Iso.inv_hom_id, Category.comp_id]

/-- 入力増大経路も標準右解像度上の実際のkernel増大を計算する。 -/
lemma scalarKernelOutputRight_model (M : ModuleCategory A D) :
    (scalarKernelDerivedBaseChangeRight φ D E P).app ((moduleToDerived A D).obj M) ≫
        (scalarKernelOutputModelComputation φ D E P M).hom =
      (kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P)).map
          (resolutionDerivedExtensionComputation φ D
            (moduleCanonicalProjectiveResolution A D) M).hom ≫
        (kernelDerivedTensorAugmentation A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).app
            ((moduleExtension φ D).obj (moduleCanonicalProjectiveResolution A D M).obj) := by
  let δ := Functor.whiskerRight (scalarExtensionHomotopyDerivedIso φ D).inv
      (kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P)) ≫
    Functor.whiskerLeft (scalarModuleExtensionHomotopy φ D)
      (scalarKernelHomotopyAugmentation (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P))
  have hn := δ.naturality
    (moduleDerivedResolutionComputation A D (moduleCanonicalProjectiveResolution A D) M).hom
  simp only [Functor.comp_map] at hn
  simp only [scalarKernelDerivedBaseChangeRight, scalarKernelOutputModelComputation,
    Iso.trans_hom, Functor.mapIso_hom, Functor.whiskerLeft_app]
  change (δ.app _) ≫ _ ≫ _ = _
  rw [← Category.assoc]
  erw [← hn]
  simp only [Category.assoc, δ, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  erw [scalarKernelOutputRight_closed φ D E P (moduleCanonicalProjectiveResolution A D M).obj]
  simp only [resolutionDerivedExtensionComputation, Functor.mapIso_hom]

end SerrePositivity.DifferentialGraded.Morita
