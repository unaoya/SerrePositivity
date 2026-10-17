module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelHomotopyNaturality
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelDerivedComparison
public import SerrePositivity.DifferentialGraded.Morita.KernelAugmentationNaturality

/-! # 導来係数変更の共通モデルと増大比較のkernel射自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma scalarKernelHomotopyAugmentation_kernel_naturality
    {P Q : BimoduleCategory A E D} (f : P ⟶ Q) :
    Functor.whiskerLeft (moduleHomotopyToDerivedClosed A D)
        ((kernelDerivedTensorOnBimoduleFunctor A D E).map f) ≫
        scalarKernelHomotopyAugmentation D E (BimoduleCategory.underlying A E D Q) =
      scalarKernelHomotopyAugmentation D E (BimoduleCategory.underlying A E D P) ≫
        Functor.whiskerRight (kernelTensorHomotopyMap A D E f)
          (moduleHomotopyToDerivedClosed A E) := by
  apply NatTrans.ext
  funext X
  obtain ⟨M⟩ := X
  change ((kernelDerivedTensorOnBimoduleFunctor A D E).map f).app
      ((moduleHomotopyToDerivedClosed A D).obj ((moduleToHomotopy A D).obj M)) ≫
      (scalarKernelHomotopyAugmentation D E (BimoduleCategory.underlying A E D Q)).app
        ((moduleToHomotopy A D).obj M) =
    (scalarKernelHomotopyAugmentation D E (BimoduleCategory.underlying A E D P)).app
        ((moduleToHomotopy A D).obj M) ≫
      (moduleHomotopyToDerivedClosed A E).map
        ((kernelTensorHomotopyMap A D E f).app ((moduleToHomotopy A D).obj M))
  rw [scalarKernelHomotopyAugmentation_app, scalarKernelHomotopyAugmentation_app]
  have hn := ((kernelDerivedTensorOnBimoduleFunctor A D E).map f).naturality
    ((moduleToHomotopyDerivedIso A D).hom.app M)
  have hi := congrArg (fun k =>
      (kernelTensorHomotopyComputation A D E (BimoduleCategory.underlying A E D P) M).inv ≫ k ≫
        (kernelTensorHomotopyComputation A D E (BimoduleCategory.underlying A E D Q) M).inv)
    (kernelTensorHomotopyComputation_kernel_naturality A D E f M)
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] at hi
  rw [← Category.assoc, ← Category.assoc]
  erw [← hn]
  have ha := congrArg (fun k => k ≫
      (kernelTensorHomotopyComputation A D E (BimoduleCategory.underlying A E D Q) M).inv)
    (kernelDerivedTensorAugmentation_kernel_naturality A D E f M)
  simp only [Category.assoc] at ha
  simp only [Category.assoc]
  erw [ha]
  erw [hi]
  rfl

variable {P Q : BimoduleCategory A E D} (f : P ⟶ Q)

/-- 係数変更後のkernel射による共通計算モデルの自然変換。 -/
def scalarKernelDerivedBaseChangeModelMap :
    scalarKernelDerivedBaseChangeModel φ D E (BimoduleCategory.underlying A E D P) ⟶
      scalarKernelDerivedBaseChangeModel φ D E (BimoduleCategory.underlying A E D Q) :=
  Functor.whiskerLeft
    (moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D) ⋙
      scalarModuleExtensionHomotopy φ D)
    (Functor.whiskerRight
      (kernelTensorHomotopyMap A' (DGBaseChange φ D) (DGBaseChange φ E)
        ((scalarKernelFunctor φ D E).map f))
      (moduleHomotopyToDerivedClosed A' (DGBaseChange φ E)))

lemma scalarKernelDerivedBaseChangeLeft_kernel_naturality :
    Functor.whiskerRight ((kernelDerivedTensorOnBimoduleFunctor A D E).map f)
        (derivedExtension φ E) ≫
        scalarKernelDerivedBaseChangeLeft φ D E (BimoduleCategory.underlying A E D Q) =
      scalarKernelDerivedBaseChangeLeft φ D E (BimoduleCategory.underlying A E D P) ≫
        scalarKernelDerivedBaseChangeModelMap φ D E f := by
  apply NatTrans.ext
  funext X
  simp only [scalarKernelDerivedBaseChangeLeft, scalarKernelDerivedBaseChangeModelMap,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hn := (scalarExtensionHomotopyAugmentation φ E).naturality
    ((kernelTensorHomotopyMap A D E f).app
      ((moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D)).obj X))
  have hb := NatTrans.congr_app
    (scalarKernelBalancedHomotopyDerivedIso_kernel_naturality φ D E f)
    ((moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D)).obj X)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hb
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc]
  erw [hb]
  exact (Category.assoc _ _ _).symm

lemma scalarKernelDerivedBaseChangeRight_kernel_naturality :
    Functor.whiskerLeft (derivedExtension φ D)
        ((kernelDerivedTensorOnBimoduleFunctor A' (DGBaseChange φ D) (DGBaseChange φ E)).map
          ((scalarKernelFunctor φ D E).map f)) ≫
        scalarKernelDerivedBaseChangeRight φ D E (BimoduleCategory.underlying A E D Q) =
      scalarKernelDerivedBaseChangeRight φ D E (BimoduleCategory.underlying A E D P) ≫
        scalarKernelDerivedBaseChangeModelMap φ D E f := by
  apply NatTrans.ext
  funext X
  simp only [scalarKernelDerivedBaseChangeRight, scalarKernelDerivedBaseChangeModelMap,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hn := ((kernelDerivedTensorOnBimoduleFunctor A' (DGBaseChange φ D)
    (DGBaseChange φ E)).map ((scalarKernelFunctor φ D E).map f)).naturality
      ((scalarExtensionHomotopyDerivedIso φ D).inv.app
        ((moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D)).obj X))
  have ha := NatTrans.congr_app
    (scalarKernelHomotopyAugmentation_kernel_naturality (DGBaseChange φ D) (DGBaseChange φ E)
      ((scalarKernelFunctor φ D E).map f))
    ((scalarModuleExtensionHomotopy φ D).obj
      ((moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D)).obj X))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at ha
  rw [← Category.assoc]
  erw [← hn]
  rw [Category.assoc]
  erw [ha]
  exact (Category.assoc _ _ _).symm

variable
  (hAugP : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E (BimoduleCategory.underlying A E D P)).onClosed.obj
        (moduleCanonicalProjectiveResolution A D M).obj)))
  (hAugQ : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E (BimoduleCategory.underlying A E D Q)).onClosed.obj
        (moduleCanonicalProjectiveResolution A D M).obj)))
  (hP' : ∀ M : ModuleCategory A D,
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A)
        (moduleCanonicalProjectiveResolution A D M).obj)))

/-- 実際の導来係数変更同型は、許容モデル間の全kernel射に自然。 -/
lemma scalarKernelDerivedBaseChangeIso_kernel_naturality :
    Functor.whiskerRight ((kernelDerivedTensorOnBimoduleFunctor A D E).map f)
        (derivedExtension φ E) ≫
        (scalarKernelDerivedBaseChangeIso φ D E (BimoduleCategory.underlying A E D Q)
          hAugQ hP').hom =
      (scalarKernelDerivedBaseChangeIso φ D E (BimoduleCategory.underlying A E D P)
        hAugP hP').hom ≫
        Functor.whiskerLeft (derivedExtension φ D)
          ((kernelDerivedTensorOnBimoduleFunctor A' (DGBaseChange φ D) (DGBaseChange φ E)).map
            ((scalarKernelFunctor φ D E).map f)) := by
  have := scalarKernelDerivedBaseChangeRight_isIso φ D E
    (BimoduleCategory.underlying A E D Q) hP'
  apply (cancel_mono (scalarKernelDerivedBaseChangeRight φ D E
    (BimoduleCategory.underlying A E D Q))).1
  simp only [Category.assoc]
  rw [scalarKernelDerivedBaseChangeIso_hom_comp_right,
    scalarKernelDerivedBaseChangeRight_kernel_naturality]
  rw [← Category.assoc, scalarKernelDerivedBaseChangeIso_hom_comp_right]
  exact scalarKernelDerivedBaseChangeLeft_kernel_naturality φ D E f

/-- U12fのhPN・hP'を明示した、導来係数変更正方形のkernel射自然性。 -/
lemma scalarKernelDerivedBaseChangeIso_ofKFlatModels_kernel_naturality
    (hE : localHomKFlat A E)
    (hPNP : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        ((BimoduleCategory.underlying A E D P).leftAt e)))
    (hPNQ : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        ((BimoduleCategory.underlying A E D Q).leftAt e))) :
    Functor.whiskerRight ((kernelDerivedTensorOnBimoduleFunctor A D E).map f)
        (derivedExtension φ E) ≫
        (scalarKernelDerivedBaseChangeIso_ofKFlatModels φ D E
          (BimoduleCategory.underlying A E D Q) hE hPNQ hP').hom =
      (scalarKernelDerivedBaseChangeIso_ofKFlatModels φ D E
        (BimoduleCategory.underlying A E D P) hE hPNP hP').hom ≫
        Functor.whiskerLeft (derivedExtension φ D)
          ((kernelDerivedTensorOnBimoduleFunctor A' (DGBaseChange φ D) (DGBaseChange φ E)).map
            ((scalarKernelFunctor φ D E).map f)) :=
  scalarKernelDerivedBaseChangeIso_kernel_naturality φ D E f
    (scalarKernelOutputAugmentation_isIso φ D E (BimoduleCategory.underlying A E D P) hE hPNP)
    (scalarKernelOutputAugmentation_isIso φ D E (BimoduleCategory.underlying A E D Q) hE hPNQ) hP'

end SerrePositivity.DifferentialGraded.Morita
