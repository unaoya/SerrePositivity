module

public import SerrePositivity.DifferentialGraded.Morita.ScalarExtension.KernelComparison
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionTensor
public import SerrePositivity.DifferentialGraded.Morita.Perfect
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
public import SerrePositivity.DifferentialGraded.Morita.Kernel
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.PerfectStability
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.EnhancementComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.HomComparison
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionComplexNaturality

/-!
# Morita.ScalarExtension.PerfectSquares

## 概要
出力評価モデルによる kernel 係数変更正方形と Perf 制限をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ScalarExtensionKernelOutputModels（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelOutputModels.lean） -/

/-! # 出力係数変更の通常モデル上の比較射計算 -/

@[expose] public section ScalarExtensionKernelOutputModels
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end ScalarExtensionKernelOutputModels

/-! ## ScalarExtensionKernelEvaluationModels（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelEvaluationModels.lean） -/

/-! # kernel評価比較の標準解像度成分 -/

@[expose] public section ScalarExtensionKernelEvaluationModels
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  [HasDerivedCategory.{z} (ModuleCat.{u} A)]

lemma scalarKernelEvaluationHomotopy_closed (e : E) (M : ModuleCategory A D) :
    (perfectKernelTensorHomotopyEvaluationIso A D E P e).hom.app
        ((moduleToHomotopy A D).obj M) ≫
        (perfectKernelU12dHomotopyTensorFacIso A D E P e).hom.app M =
      (perfectKernelTensorHomotopyEvaluationFacIso A D E P e).hom.app M := by
  simp only [perfectKernelTensorHomotopyEvaluationIso, Quotient.natIsoLift_hom,
    Quotient.natTransLift_app, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc]
  change _ ≫ ((perfectKernelU12dHomotopyTensorFacIso A D E P e).app M).inv ≫
    ((perfectKernelU12dHomotopyTensorFacIso A D E P e).app M).hom = _
  rw [Iso.inv_hom_id, Category.comp_id]

lemma scalarKernelEvaluationClosed_fac (e : E) (M : ModuleCategory A D) :
    (perfectKernelTensorHomotopyEvaluationFacIso A D E P e).hom.app M =
      (moduleDerivedEvaluation A E e).map (kernelTensorHomotopyComputation A D E P M).hom ≫
        (eqToIso (moduleDerivedEvaluation_fac A E e)).hom.app
          ((kernelTensor A D E P).onClosed.obj M) := by
  simp only [perfectKernelTensorHomotopyEvaluationFacIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    moduleDerivedEvaluationHomotopyFacIso, perfectKernelTensorEvaluationIso,
    NatIso.ofComponents, Iso.refl_hom, CategoryTheory.Functor.map_id,
    Category.id_comp, eqToIso.hom]
  rw [scalarKernelOutputHomotopyComputation_hom]
  simp only [eqToHom_refl, eqToHom_app, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [Category.id_comp, Category.comp_id, Category.comp_id]

lemma scalarKernelU12dClosed_fac (e : E) (M : ModuleCategory A D) :
    (perfectKernelU12dHomotopyTensorFacIso A D E P e).hom.app M =
      DerivedCategory.Qh.map (moduleTensorHomotopyComputation A D (P.leftAt e) M).hom ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app
          ((BalancedTensor.rightTensorFunctor A D (P.leftAt e)).obj M) := by
  simp only [perfectKernelU12dHomotopyTensorFacIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    eqToIso.hom, eqToHom_app]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  change 𝟙 _ ≫ _ = DerivedCategory.Qh.map (𝟙 _) ≫ _
  rw [CategoryTheory.Functor.map_id]

/-- U12d評価比較とkernel計算の標準解像度成分は一致する。 -/
lemma scalarKernelResolutionEvaluation_computation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (e : E) (M : ModuleCategory A D) :
    (moduleDerivedEvaluation A E e).map
        (kernelResolutionDerivedTensorComputation A D E P R M).hom ≫
        (eqToIso (moduleDerivedEvaluation_fac A E e)).hom.app
          ((kernelTensor A D E P).onClosed.obj (R M).obj) =
      (perfectKernelResolutionDerivedTensorEvaluationIso A D E P R e).hom.app
          ((moduleToDerived A D).obj M) ≫
        (moduleResolutionDerivedTensorComputation A D R (P.leftAt e) M).hom := by
  have hn := (perfectKernelTensorHomotopyEvaluationIso A D E P e).hom.naturality
    (moduleDerivedResolutionComputation A D R M).hom
  simp only [Functor.comp_map] at hn
  simp only [perfectKernelResolutionDerivedTensorEvaluationIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp]
  erw [Category.id_comp]
  simp only [moduleResolutionDerivedTensorComputation, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map]
  rw [← Category.assoc]
  erw [← hn]
  simp only [Category.assoc]
  erw [← scalarKernelU12dClosed_fac, scalarKernelEvaluationHomotopy_closed,
    scalarKernelEvaluationClosed_fac]
  simp only [kernelResolutionDerivedTensorComputation, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- 相対K-flat入力でのU12d計算と、実際のkernel増大の評価は一致する。 -/
lemma scalarKernelEvaluationAugmentation_relativeKFlat (e : E) (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (moduleDerivedEvaluation A E e).map ((kernelDerivedTensorAugmentation A D E P).app M) ≫
        (eqToIso (moduleDerivedEvaluation_fac A E e)).hom.app
          ((kernelTensor A D E P).onClosed.obj M) =
      (perfectKernelDerivedTensorEvaluationIso A D E P e).hom.app ((moduleToDerived A D).obj M) ≫
        (ScalarExtension.relativeKFlatTensorComputation D M hM (P.leftAt e)).hom := by
  rw [kernelDerivedTensorAugmentation_app, CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (eqToIso (moduleDerivedEvaluation_fac A E e)).hom.naturality
    ((kernelTensor A D E P).onClosed.map (moduleCanonicalProjectiveResolution A D M).π)
  simp only [Functor.comp_map] at hn
  erw [hn]
  rw [← Category.assoc, scalarKernelResolutionEvaluation_computation]
  simp only [ScalarExtension.relativeKFlatTensorComputation, Iso.trans_hom, asIso_hom,
    Category.assoc]
  simp only [moduleEvaluationToDerived, Functor.comp_map]
  rw [perfectKernelTensor_map_eval]
  rfl

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelEvaluationModels

/-! ## ScalarExtensionKernelDerivedNaturality（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelDerivedNaturality.lean） -/

/-! # 導来係数変更の共通モデルと増大比較のkernel射自然性 -/

@[expose] public section ScalarExtensionKernelDerivedNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end ScalarExtensionKernelDerivedNaturality

/-! ## ScalarExtensionKernelBaseChangeNaturality（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelBaseChangeNaturality.lean） -/

/-! # kernel射に自然な、実際の作用評価のU12f係数変更比較

指定右解像度についてhPN・hP'を満たすkernelの充満部分圏上で自然同型を構成する。
始域は出力評価の複体の導来係数変更であり、出力dg加群の係数変更との交換は含めない。
-/

@[expose] public section ScalarExtensionKernelBaseChangeNaturality
universe u v w z z'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  [HasDerivedCategory.{z} (ModuleCat.{u} A)]
  [HasDerivedCategory.{z'} (ModuleCat.{u} A')]

/-- kernelの左評価ごとのhPNと、係数変更した右モデルのhP'を保持する。 -/
def scalarKernelBaseChangeModels (e : E) {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) : ObjectProperty (BimoduleCategory A E D) :=
  (scalarTensorLeftModels D φ R).inverseImage (BimoduleCategory.leftEvaluation A E D e)

def scalarKernelBaseChangeLeftModelsFunctor (e : E) {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) :
    (scalarKernelBaseChangeModels φ D E e R).FullSubcategory ⥤
      (scalarTensorLeftModels D φ R).FullSubcategory :=
  (scalarTensorLeftModels D φ R).lift
    ((scalarKernelBaseChangeModels φ D E e R).ι ⋙ BimoduleCategory.leftEvaluation A E D e)
    (fun P => P.property)

def scalarKernelBaseChangeSource (e : E) (M : ModuleCategory A D) :
    BimoduleCategory A E D ⥤ DerivedCategory (ModuleCat.{u} A') :=
  kernelDerivedEvaluationFunctor A D E e ⋙
    (CategoryTheory.evaluation (DerivedModuleCategory A D)
      (DerivedCategory (ModuleCat.{u} A))).obj ((moduleToDerived A D).obj M) ⋙
        complexDerivedExtension φ

def scalarKernelBaseChangeTarget (e : E) (M : ModuleCategory A D) :
    BimoduleCategory A E D ⥤ DerivedCategory (ModuleCat.{u} A') :=
  scalarKernelFunctor φ D E ⋙
    kernelDerivedEvaluationFunctor A' (DGBaseChange φ D) (DGBaseChange φ E) e ⋙
      (CategoryTheory.evaluation (DerivedModuleCategory A' (DGBaseChange φ D))
        (DerivedCategory (ModuleCat.{u} A'))).obj
          ((derivedExtension φ D).obj ((moduleToDerived A D).obj M))

/-- kernel射に自然な、U12fと実際の導来kernel作用評価の比較。 -/
def scalarKernelBaseChangeIso (e : E) {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) :
    (scalarKernelBaseChangeModels φ D E e R).ι ⋙ scalarKernelBaseChangeSource φ D E e M ≅
      (scalarKernelBaseChangeModels φ D E e R).ι ⋙ scalarKernelBaseChangeTarget φ D E e M :=
  Functor.isoWhiskerLeft (scalarKernelBaseChangeModels φ D E e R).ι
      (Functor.isoWhiskerRight (kernelDerivedEvaluationIso A D E e)
        ((CategoryTheory.evaluation (DerivedModuleCategory A D)
          (DerivedCategory (ModuleCat.{u} A))).obj ((moduleToDerived A D).obj M) ⋙
            complexDerivedExtension φ)) ≪≫
    Functor.isoWhiskerLeft (scalarKernelBaseChangeLeftModelsFunctor φ D E e R)
      (scalarTensorBaseChangeLeftIso D φ R) ≪≫
    (Functor.isoWhiskerLeft
        ((scalarKernelBaseChangeModels φ D E e R).ι ⋙ scalarKernelFunctor φ D E)
        (Functor.isoWhiskerRight
          (kernelDerivedEvaluationIso A' (DGBaseChange φ D) (DGBaseChange φ E) e)
          ((CategoryTheory.evaluation (DerivedModuleCategory A' (DGBaseChange φ D))
            (DerivedCategory (ModuleCat.{u} A'))).obj
              ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)))) ≪≫
      Functor.isoWhiskerLeft (scalarKernelBaseChangeModels φ D E e R).ι
        (Functor.isoWhiskerRight (scalarKernelLeftEvaluationIso φ D E e)
          (moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D) ⋙
            (CategoryTheory.evaluation (DerivedModuleCategory A' (DGBaseChange φ D))
              (DerivedCategory (ModuleCat.{u} A'))).obj
                ((derivedExtension φ D).obj ((moduleToDerived A D).obj M))))).symm

/-- この自然同型の成分には、既存U12fの比較射をそのまま使う。 -/
lemma scalarKernelBaseChangeIso_hom_app (e : E) {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M)
    (P : (scalarKernelBaseChangeModels φ D E e R).FullSubcategory) :
    (scalarKernelBaseChangeIso φ D E e R).hom.app P =
      (complexDerivedExtension φ).map
          ((perfectKernelDerivedTensorEvaluationIso A D E
            (BimoduleCategory.underlying A E D P.obj) e).hom.app
              ((moduleToDerived A D).obj M)) ≫
        (derivedTensorBaseChange φ D R
          ((BimoduleCategory.underlying A E D P.obj).leftAt e)
          P.property.1 P.property.2).hom ≫
        ((moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
          ((scalarKernelLeftEvaluationIso φ D E e).inv.app P.obj)).app
            ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) ≫
        (perfectKernelDerivedTensorEvaluationIso A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E (BimoduleCategory.underlying A E D P.obj)) e).inv.app
            ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) := rfl

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelBaseChangeNaturality

/-! ## ScalarExtensionPerfect（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionPerfect.lean） -/

/-! # U16d：非flatな導来係数変更の主Perf制限

U14で証明した射影的perfect代表の実際の係数拡大のperfect性を、
U12fの既存導来係数拡大の任意射影解像度計算で主導来圏へ接続する。
-/

@[expose] public section ScalarExtensionPerfect
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarDerivedExtension_perfectOver {S : Set D} {X : DerivedModuleCategory A D}
    (hX : modulePerfectOver A D S X) :
    modulePerfectOver A' (DGBaseChange φ D) (scalarPerfectGenerators φ D S)
      ((derivedExtension φ D).obj X) := by
  obtain ⟨⟨M⟩⟩ := X
  let P := moduleCanonicalProjectiveResolution A D M
  have hP : modulePerfectOver A D S ((moduleToDerived A D).obj P.obj) :=
    (modulePerfectOver A D S).prop_of_iso (moduleDerivedIso A D P.π P.quasiIso).symm hX
  exact (modulePerfectOver A' (DGBaseChange φ D) (scalarPerfectGenerators φ D S)).prop_of_iso
    (derivedExtensionResolutionComputation φ D P).symm
    (scalarModuleExtension_perfect_perfect φ D P.projective hP)

lemma scalarDerivedExtension_perfect {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A' (DGBaseChange φ D) ((derivedExtension φ D).obj X) :=
  scalarDerivedExtension_perfectOver φ D hX

def scalarExtensionPerfectFunctor (S : Set D) :
    PerfectModuleCategoryOver A D S ⥤
      PerfectModuleCategoryOver A' (DGBaseChange φ D) (scalarPerfectGenerators φ D S) :=
  (modulePerfectOver A' (DGBaseChange φ D) (scalarPerfectGenerators φ D S)).lift
    (perfectModuleInclusion A D S ⋙ derivedExtension φ D)
    (fun X => scalarDerivedExtension_perfectOver φ D X.property)

def scalarExtensionPerfectInclusionIso (S : Set D) :
    scalarExtensionPerfectFunctor φ D S ⋙
        perfectModuleInclusion A' (DGBaseChange φ D) (scalarPerfectGenerators φ D S) ≅
      perfectModuleInclusion A D S ⋙ derivedExtension φ D := Iso.refl _

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionPerfect

/-! ## ScalarExtensionPerfectSquares（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionPerfectSquares.lean） -/

/-! # U16d：係数変更正方形の実際の主Perf制限と自然性

主導来圏上の指定された係数変更正方形を入力し、実際の非flat係数変更のPerf制限へ移す。
未実装のkernel作用の正方形を証明済みとは仮定しない。kernel固有の入力は明示したまま使う。
-/

@[expose] public section ScalarExtensionPerfectSquares
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

def scalarPerfectSquare
    (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (T' : DerivedModuleCategory A' (DGBaseChange φ D) ⥤
      DerivedModuleCategory A' (DGBaseChange φ E))
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hT' : ∀ X, modulePerfect A' (DGBaseChange φ D) X →
      modulePerfect A' (DGBaseChange φ E) (T'.obj X))
    (e : T ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ T') :
    perfectFunctorRestriction A D E T hT ⋙ scalarExtensionPerfectFunctor φ E Set.univ ≅
      scalarExtensionPerfectFunctor φ D Set.univ ⋙
        perfectFunctorRestriction A' (DGBaseChange φ D) (DGBaseChange φ E) T' hT' :=
  NatIso.ofComponents (fun X => (modulePerfect A' (DGBaseChange φ E)).isoMk (e.app X.obj))
    (by intro X Y f
        exact (modulePerfect A' (DGBaseChange φ E)).hom_ext (e.hom.naturality f.hom))

lemma scalarPerfectSquare_inclusion
    (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (T' : DerivedModuleCategory A' (DGBaseChange φ D) ⥤
      DerivedModuleCategory A' (DGBaseChange φ E))
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hT' : ∀ X, modulePerfect A' (DGBaseChange φ D) X →
      modulePerfect A' (DGBaseChange φ E) (T'.obj X))
    (e : T ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ T') :
    Functor.whiskerRight (scalarPerfectSquare φ D E T T' hT hT' e).hom
        (perfectModuleInclusion A' (DGBaseChange φ E) Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ) e.hom := rfl

lemma scalarPerfectSquare_naturality
    (T U : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (T' U' : DerivedModuleCategory A' (DGBaseChange φ D) ⥤
      DerivedModuleCategory A' (DGBaseChange φ E))
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hU : ∀ X, modulePerfect A D X → modulePerfect A E (U.obj X))
    (hT' : ∀ X, modulePerfect A' (DGBaseChange φ D) X →
      modulePerfect A' (DGBaseChange φ E) (T'.obj X))
    (hU' : ∀ X, modulePerfect A' (DGBaseChange φ D) X →
      modulePerfect A' (DGBaseChange φ E) (U'.obj X))
    (eT : T ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ T')
    (eU : U ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ U')
    (α : T ⟶ U) (α' : T' ⟶ U')
    (hα : Functor.whiskerRight α (derivedExtension φ E) ≫ eU.hom =
      eT.hom ≫ Functor.whiskerLeft (derivedExtension φ D) α') :
    Functor.whiskerRight (perfectFunctorTransformation A D E T U hT hU α)
        (scalarExtensionPerfectFunctor φ E Set.univ) ≫
        (scalarPerfectSquare φ D E U U' hU hU' eU).hom =
      (scalarPerfectSquare φ D E T T' hT hT' eT).hom ≫
        Functor.whiskerLeft (scalarExtensionPerfectFunctor φ D Set.univ)
          (perfectFunctorTransformation A' (DGBaseChange φ D) (DGBaseChange φ E)
            T' U' hT' hU' α') := by
  apply NatTrans.ext
  funext X
  apply (modulePerfect A' (DGBaseChange φ E)).hom_ext
  exact NatTrans.congr_app hα X.obj

section Composition

variable (B : Type z) [DGCategory A B] [Small.{u} B]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  (U : DerivedModuleCategory A E ⥤ DerivedModuleCategory A B)
  (T' : DerivedModuleCategory A' (DGBaseChange φ D) ⥤
    DerivedModuleCategory A' (DGBaseChange φ E))
  (U' : DerivedModuleCategory A' (DGBaseChange φ E) ⥤
    DerivedModuleCategory A' (DGBaseChange φ B))
  (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
  (hU : ∀ X, modulePerfect A E X → modulePerfect A B (U.obj X))
  (hT' : ∀ X, modulePerfect A' (DGBaseChange φ D) X →
    modulePerfect A' (DGBaseChange φ E) (T'.obj X))
  (hU' : ∀ X, modulePerfect A' (DGBaseChange φ E) X →
    modulePerfect A' (DGBaseChange φ B) (U'.obj X))
  (eT : T ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ T')
  (eU : U ⋙ derivedExtension φ B ≅ derivedExtension φ E ⋙ U')

/-- 二つの主導来係数変更正方形の合成。 -/
def scalarDerivedSquareComposition :
    (T ⋙ U) ⋙ derivedExtension φ B ≅ derivedExtension φ D ⋙ (T' ⋙ U') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T eU ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eT U' ≪≫
    Functor.associator _ _ _

/-- 実際の主Perf制限の合成同型も含めて、二つの係数変更正方形を合成する。 -/
def scalarPerfectSquareComposition :
    perfectFunctorRestriction A D B (T ⋙ U) (fun X h => hU _ (hT X h)) ⋙
        scalarExtensionPerfectFunctor φ B Set.univ ≅
      scalarExtensionPerfectFunctor φ D Set.univ ⋙
        perfectFunctorRestriction A' (DGBaseChange φ D) (DGBaseChange φ B) (T' ⋙ U')
          (fun X h => hU' _ (hT' X h)) :=
  Functor.isoWhiskerRight (perfectFunctorCompositionIso A D E B T U hT hU).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarPerfectSquare φ E B U U' hU hU' eU) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarPerfectSquare φ D E T T' hT hT' eT) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (perfectFunctorCompositionIso A' (DGBaseChange φ D) (DGBaseChange φ E)
        (DGBaseChange φ B) T' U' hT' hU')

/-- 主導来正方形を合成してから制限する経路と、主Perf正方形を合成する経路は一致する。 -/
lemma scalarPerfectSquareComposition_eq :
    scalarPerfectSquare φ D B (T ⋙ U) (T' ⋙ U')
        (fun X h => hU _ (hT X h)) (fun X h => hU' _ (hT' X h))
        (scalarDerivedSquareComposition φ D E B T U T' U' eT eU) =
      scalarPerfectSquareComposition φ D E B T U T' U' hT hU hT' hU' eT eU := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (modulePerfect A' (DGBaseChange φ B)).hom_ext
  simp only [scalarPerfectSquareComposition, scalarPerfectSquare, scalarDerivedSquareComposition,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, perfectFunctorCompositionIso,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, NatIso.ofComponents, ObjectProperty.isoMk,
    Iso.app_hom]
  simp only [Category.id_comp, Category.comp_id]
  change eU.hom.app (T.obj X.obj) ≫ U'.map (eT.hom.app X.obj) =
    (derivedExtension φ B).map (𝟙 _) ≫ eU.hom.app (T.obj X.obj) ≫
      U'.map (eT.hom.app X.obj) ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end Composition

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionPerfectSquares

/-! ## ScalarExtensionKernelPerfectSquare（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelPerfectSquare.lean） -/

/-! # 実際のkernel導来係数変更正方形のPerf制限

係数変更後の列のperfect性も元の列と実際の導来正方形から証明する。
-/

@[expose] public section ScalarExtensionKernelPerfectSquare
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 導来係数変更は代表加群を実際の係数変更後の代表加群へ送る。 -/
def scalarDerivedRepresentableIso (d : D) :
    (derivedExtension φ D).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≅
      (moduleToDerived A' (DGBaseChange φ D)).obj
        (ForgetEnrichment.of (Complex A') (representable A' (show DGBaseChange φ D from d))) :=
  scalarDerivedProjectiveComputation φ D
      (ForgetEnrichment.of (Complex A) (representable A d))
      (representable_homotopicallyProjective A D d) ≪≫
    (moduleToDerived A' (DGBaseChange φ D)).mapIso
      (eqToIso (congrArg (ForgetEnrichment.of (Complex A')) (scalarRepresentable_eq φ D d)))

variable (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 代表入力での通常kernelの実際の導来作用は右列を計算する。 -/
def scalarKernelRawColumnIso (d : D) :
    (kernelDerivedTensorOnBimodule A D E P).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≅
      (moduleToDerived A E).obj (ForgetEnrichment.of (Complex A) (P.rightAt d)) :=
  ((kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D P)).symm).app _ ≪≫
    kernelDerivedColumnActionIso A D E
      ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)) d ≪≫
    kernelDerivedColumnComputation A D E d (BimoduleCategory.of A E D P)

lemma scalarKernelDerivedBaseChange_columnsPerfect
    (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt d))))
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    ∀ d : DGBaseChange φ D, modulePerfect A' (DGBaseChange φ E)
      ((moduleToDerived A' (DGBaseChange φ E)).obj
        (ForgetEnrichment.of (Complex A') ((scalarKernel φ D E P).rightAt d))) := by
  intro d
  let X := (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))
  let e := (scalarKernelDerivedBaseChangeIso φ D E P hAug hP').app X ≪≫
    (kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P)).mapIso (scalarDerivedRepresentableIso φ D d) ≪≫
    scalarKernelRawColumnIso (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P) d
  have hX : modulePerfect A D X := modulePerfectOver_representable A D d (Set.mem_univ _)
  exact (modulePerfect A' (DGBaseChange φ E)).prop_of_iso e
    (scalarDerivedExtension_perfect φ E (perfectKernelAction_preserves A D E P hP hX))

/-- 係数変更後の列のperfect性を追加仮定せず、実際の導来比較をPerfへ制限する。 -/
def scalarKernelPerfectDerivedSquare
    (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt d))))
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    perfectKernelAction A D E P hP ⋙ scalarExtensionPerfectFunctor φ E Set.univ ≅
      scalarExtensionPerfectFunctor φ D Set.univ ⋙
        perfectKernelAction A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)
          (scalarKernelDerivedBaseChange_columnsPerfect φ D E P hP hAug hP') :=
  scalarPerfectSquare φ D E (kernelDerivedTensorOnBimodule A D E P)
    (kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P))
    (fun _ h => perfectKernelAction_preserves A D E P hP h)
    (fun _ h => perfectKernelAction_preserves A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P) (scalarKernelDerivedBaseChange_columnsPerfect φ D E P hP hAug hP') h)
    (scalarKernelDerivedBaseChangeIso φ D E P hAug hP')

lemma scalarKernelPerfectDerivedSquare_inclusion
    (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt d))))
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    Functor.whiskerRight (scalarKernelPerfectDerivedSquare φ D E P hP hAug hP').hom
        (perfectModuleInclusion A' (DGBaseChange φ E) Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ)
        (scalarKernelDerivedBaseChangeIso φ D E P hAug hP').hom := rfl

/-- 出力の局所Hom条件とhPN・hP'を保持した、実際のPerf係数変更正方形。 -/
def scalarKernelPerfectDerivedSquare_ofKFlatModels
    (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt d))))
    (hE : localHomKFlat A E)
    (hPN : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        (P.leftAt e)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    perfectKernelAction A D E P hP ⋙ scalarExtensionPerfectFunctor φ E Set.univ ≅
      scalarExtensionPerfectFunctor φ D Set.univ ⋙
        perfectKernelAction A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)
          (scalarKernelDerivedBaseChange_columnsPerfect φ D E P hP
            (scalarKernelOutputAugmentation_isIso φ D E P hE hPN) hP') :=
  scalarKernelPerfectDerivedSquare φ D E P hP
    (scalarKernelOutputAugmentation_isIso φ D E P hE hPN) hP'

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelPerfectSquare

/-! ## ScalarExtensionKernelPerfectNaturality（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelPerfectNaturality.lean） -/

/-! # 実際のPerf係数変更正方形のkernel射自然性 -/

@[expose] public section ScalarExtensionKernelPerfectNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  {P Q : BimoduleCategory A E D} (f : P ⟶ Q)
  (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
    (ForgetEnrichment.of (Complex A) ((BimoduleCategory.underlying A E D P).rightAt d))))
  (hQ : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
    (ForgetEnrichment.of (Complex A) ((BimoduleCategory.underlying A E D Q).rightAt d))))

/-- 列がperfectな通常kernel間の射を、実際のPerf作用の射へ制限する。 -/
def perfectKernelBimoduleMap :
    perfectKernelAction A D E (BimoduleCategory.underlying A E D P) hP ⟶
      perfectKernelAction A D E (BimoduleCategory.underlying A E D Q) hQ :=
  perfectFunctorTransformation A D E _ _
    (fun _ h => perfectKernelAction_preserves A D E (BimoduleCategory.underlying A E D P) hP h)
    (fun _ h => perfectKernelAction_preserves A D E (BimoduleCategory.underlying A E D Q) hQ h)
    ((kernelDerivedTensorOnBimoduleFunctor A D E).map f)

lemma perfectKernelBimoduleMap_inclusion :
    Functor.whiskerRight (perfectKernelBimoduleMap D E f hP hQ)
        (perfectModuleInclusion A E Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ)
        ((kernelDerivedTensorOnBimoduleFunctor A D E).map f) := rfl

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

/-- Perf正方形の比較射は、モデル条件を満たすkernelの全閉零射に自然。 -/
lemma scalarKernelPerfectDerivedSquare_kernel_naturality :
    Functor.whiskerRight (perfectKernelBimoduleMap D E f hP hQ)
        (scalarExtensionPerfectFunctor φ E Set.univ) ≫
        (scalarKernelPerfectDerivedSquare φ D E (BimoduleCategory.underlying A E D Q)
          hQ hAugQ hP').hom =
      (scalarKernelPerfectDerivedSquare φ D E (BimoduleCategory.underlying A E D P)
        hP hAugP hP').hom ≫
        Functor.whiskerLeft (scalarExtensionPerfectFunctor φ D Set.univ)
          (perfectKernelBimoduleMap (DGBaseChange φ D) (DGBaseChange φ E)
            ((scalarKernelFunctor φ D E).map f)
            (scalarKernelDerivedBaseChange_columnsPerfect φ D E
              (BimoduleCategory.underlying A E D P) hP hAugP hP')
            (scalarKernelDerivedBaseChange_columnsPerfect φ D E
              (BimoduleCategory.underlying A E D Q) hQ hAugQ hP')) :=
  scalarPerfectSquare_naturality φ D E _ _ _ _ _ _ _ _ _ _ _ _
    (scalarKernelDerivedBaseChangeIso_kernel_naturality φ D E f hAugP hAugQ hP')

/-- hPN・hP'を保持した実際のPerf正方形もkernel射に自然。 -/
lemma scalarKernelPerfectDerivedSquare_ofKFlatModels_kernel_naturality
    (hE : localHomKFlat A E)
    (hPNP : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        ((BimoduleCategory.underlying A E D P).leftAt e)))
    (hPNQ : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        ((BimoduleCategory.underlying A E D Q).leftAt e))) :
    Functor.whiskerRight (perfectKernelBimoduleMap D E f hP hQ)
        (scalarExtensionPerfectFunctor φ E Set.univ) ≫
        (scalarKernelPerfectDerivedSquare_ofKFlatModels φ D E
          (BimoduleCategory.underlying A E D Q) hQ hE hPNQ hP').hom =
      (scalarKernelPerfectDerivedSquare_ofKFlatModels φ D E
        (BimoduleCategory.underlying A E D P) hP hE hPNP hP').hom ≫
        Functor.whiskerLeft (scalarExtensionPerfectFunctor φ D Set.univ)
          (perfectKernelBimoduleMap (DGBaseChange φ D) (DGBaseChange φ E)
            ((scalarKernelFunctor φ D E).map f)
            (scalarKernelDerivedBaseChange_columnsPerfect φ D E
              (BimoduleCategory.underlying A E D P) hP
              (scalarKernelOutputAugmentation_isIso φ D E
                (BimoduleCategory.underlying A E D P) hE hPNP) hP')
            (scalarKernelDerivedBaseChange_columnsPerfect φ D E
              (BimoduleCategory.underlying A E D Q) hQ
              (scalarKernelOutputAugmentation_isIso φ D E
                (BimoduleCategory.underlying A E D Q) hE hPNQ) hP')) :=
  scalarKernelPerfectDerivedSquare_kernel_naturality φ D E f hP hQ
    (scalarKernelOutputAugmentation_isIso φ D E (BimoduleCategory.underlying A E D P) hE hPNP)
    (scalarKernelOutputAugmentation_isIso φ D E (BimoduleCategory.underlying A E D Q) hE hPNQ) hP'

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelPerfectNaturality

/-! ## ScalarExtensionKernelLocalizedSquare（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelLocalizedSquare.lean） -/

/-! # 局所化したkernel係数変更への実際の作用正方形

通常モデルへの増大の可逆性を明示し、既存のdg加群値の比較を主kernelの
係数変更関手へ接続する。増大の可逆性をhPN・hP'から推論しない。
-/

@[expose] public section ScalarExtensionKernelLocalizedSquare
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (P : BimoduleCategory A E D)
  (hα : IsIso ((scalarKernelDerivedExtensionAugmentation φ D E).app P))

/-- 主kernel係数変更の作用を、増大で通常係数変更モデルの作用へ比較する。 -/
def scalarKernelLocalizedActionIso :
    kernelDerivedTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
        ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P)) ≅
      kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E (BimoduleCategory.underlying A E D P)) := by
  let := hα
  exact (kernelDerivedTensorFunctor A' (DGBaseChange φ D) (DGBaseChange φ E)).mapIso
      (asIso ((scalarKernelDerivedExtensionAugmentation φ D E).app P)) ≪≫
    kernelDerivedTensorOnBimoduleIso A' (DGBaseChange φ D) (DGBaseChange φ E)
      ((scalarKernelFunctor φ D E).obj P)

variable
  (hAug : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E (BimoduleCategory.underlying A E D P)).onClosed.obj
        (moduleCanonicalProjectiveResolution A D M).obj)))
  (hP' : ∀ M : ModuleCategory A D,
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A)
        (moduleCanonicalProjectiveResolution A D M).obj)))

/-- 通常モデルの正方形を、実際の主局所化kernel係数変更の作用へ接続する。 -/
def scalarKernelLocalizedDerivedSquare :
    kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P) ⋙ derivedExtension φ E ≅
      derivedExtension φ D ⋙
        kernelDerivedTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
          ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P)) :=
  Functor.isoWhiskerRight (kernelDerivedTensorOnBimoduleIso A D E P) _ ≪≫
    scalarKernelDerivedBaseChangeIso φ D E (BimoduleCategory.underlying A E D P) hAug hP' ≪≫
    Functor.isoWhiskerLeft (derivedExtension φ D) (scalarKernelLocalizedActionIso φ D E P hα).symm

/-- 増大後の局所化正方形は、既存の通常モデルの比較そのものである。 -/
lemma scalarKernelLocalizedDerivedSquare_augmentation :
    (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP').hom ≫
        Functor.whiskerLeft (derivedExtension φ D) (scalarKernelLocalizedActionIso φ D E P hα).hom =
      Functor.whiskerRight (kernelDerivedTensorOnBimoduleIso A D E P).hom (derivedExtension φ E) ≫
        (scalarKernelDerivedBaseChangeIso φ D E
          (BimoduleCategory.underlying A E D P) hAug hP').hom := by
  simp only [scalarKernelLocalizedDerivedSquare, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Category.assoc]
  rw [← Functor.whiskerLeft_comp, Iso.inv_hom_id]
  simp only [Functor.whiskerLeft_id', Category.comp_id]

include hα hAug hP' in
/-- 元の列がperfectなら、局所化した係数変更kernelも列がperfectである。 -/
lemma scalarKernelLocalized_columnsPerfect
    (hP : kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P)) :
    kernelColumnsPerfect A' (DGBaseChange φ D) (DGBaseChange φ E)
      ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P)) := by
  apply (kernelColumnsPerfect_iff_preservesPerfect A' (DGBaseChange φ D) (DGBaseChange φ E) _).2
  have hraw := (kernelColumnsPerfect_ofBimodule_iff A D E P).1 hP
  have hscalar := scalarKernelDerivedBaseChange_columnsPerfect φ D E
    (BimoduleCategory.underlying A E D P) hraw hAug hP'
  intro X hX
  exact (modulePerfect A' (DGBaseChange φ E)).prop_of_iso
    ((scalarKernelLocalizedActionIso φ D E P hα).app X).symm
    (perfectKernelAction_preserves A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E (BimoduleCategory.underlying A E D P)) hscalar hX)

/-- 局所化したkernel係数変更への正方形を、両側の実際のPerf作用へ制限する。 -/
def scalarKernelLocalizedPerfectSquare
    (hP : kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P)) :
    perfectDerivedKernelAction A D E ((bimoduleToDerived A E D).obj P) hP ⋙
        scalarExtensionPerfectFunctor φ E Set.univ ≅
      scalarExtensionPerfectFunctor φ D Set.univ ⋙
        perfectDerivedKernelAction A' (DGBaseChange φ D) (DGBaseChange φ E)
          ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
          (scalarKernelLocalized_columnsPerfect φ D E P hα hAug hP' hP) :=
  scalarPerfectSquare φ D E _ _
    (fun _ h => perfectDerivedKernelAction_preserves A D E _ hP h)
    (fun _ h => perfectDerivedKernelAction_preserves A' (DGBaseChange φ D) (DGBaseChange φ E) _
      (scalarKernelLocalized_columnsPerfect φ D E P hα hAug hP' hP) h)
    (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP')

lemma scalarKernelLocalizedPerfectSquare_inclusion
    (hP : kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P)) :
    Functor.whiskerRight (scalarKernelLocalizedPerfectSquare φ D E P hα hAug hP' hP).hom
        (perfectModuleInclusion A' (DGBaseChange φ E) Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ)
        (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP').hom := rfl

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelLocalizedSquare

/-! ## ScalarExtensionKernelLocalizedComposition（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelLocalizedComposition.lean） -/

/-! # 局所化kernel係数変更の作用正方形と実際のkernel合成

通常代表のモデル条件を保持し、公開kernelCompositionIsoを両側に使う。
係数変更関手が合成kernelを保存する同型の存在は入力にも結論にも含めない。
-/

@[expose] public section ScalarExtensionKernelLocalizedComposition
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 通常モデルから局所化係数変更への作用正方形に必要な三つの条件。 -/
structure ScalarKernelLocalizedConditions (P : BimoduleCategory A E D) : Prop where
  augmentationIsIso : IsIso ((scalarKernelDerivedExtensionAugmentation φ D E).app P)
  outputAugmentation : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E (BimoduleCategory.underlying A E D P)).onClosed.obj
        (moduleCanonicalProjectiveResolution A D M).obj))
  inputRelativeKFlat : ∀ M : ModuleCategory A D,
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A)
        (moduleCanonicalProjectiveResolution A D M).obj))

variable (B : Type z) [DGCategory A B] [Small.{u} B]
  (hD : localHomKFlat A D) (hD' : localHomKFlat A' (DGBaseChange φ D))
  (P : BimoduleCategory A E D) (Q : BimoduleCategory A B E)
  (cP : ScalarKernelLocalizedConditions φ D E P)
  (cQ : ScalarKernelLocalizedConditions φ E B Q)

/-- 実際のkernel合成比較を両側に用いる、二つの係数変更正方形の貼合せ。 -/
def scalarKernelLocalizedCompositionSquare :
    kernelDerivedTensor A D B
        (kernelCompose A D E B hD ((bimoduleToDerived A E D).obj P)
          ((bimoduleToDerived A B E).obj Q)) ⋙ derivedExtension φ B ≅
      derivedExtension φ D ⋙ kernelDerivedTensor A' (DGBaseChange φ D) (DGBaseChange φ B)
        (kernelCompose A' (DGBaseChange φ D) (DGBaseChange φ E) (DGBaseChange φ B) hD'
          ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
          ((scalarKernelDerivedExtension φ E B).obj ((bimoduleToDerived A B E).obj Q))) :=
  Functor.isoWhiskerRight
      (kernelCompositionIso A D E B hD ((bimoduleToDerived A E D).obj P)
        ((bimoduleToDerived A B E).obj Q)).symm (derivedExtension φ B) ≪≫
    scalarDerivedSquareComposition φ D E B _ _ _ _
      (scalarKernelLocalizedDerivedSquare φ D E P cP.augmentationIsIso
        cP.outputAugmentation cP.inputRelativeKFlat)
      (scalarKernelLocalizedDerivedSquare φ E B Q cQ.augmentationIsIso
        cQ.outputAugmentation cQ.inputRelativeKFlat) ≪≫
    Functor.isoWhiskerLeft (derivedExtension φ D)
      (kernelCompositionIso A' (DGBaseChange φ D) (DGBaseChange φ E) (DGBaseChange φ B) hD'
        ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
        ((scalarKernelDerivedExtension φ E B).obj ((bimoduleToDerived A B E).obj Q)))

/-- 実際の合成比較とモデル条件付き正方形の貼合せが可換となる図式。 -/
lemma scalarKernelLocalizedCompositionSquare_diagram :
    Functor.whiskerRight
        (kernelCompositionIso A D E B hD ((bimoduleToDerived A E D).obj P)
          ((bimoduleToDerived A B E).obj Q)).hom (derivedExtension φ B) ≫
        (scalarKernelLocalizedCompositionSquare φ D E B hD hD' P Q cP cQ).hom =
      (scalarDerivedSquareComposition φ D E B _ _ _ _
        (scalarKernelLocalizedDerivedSquare φ D E P cP.augmentationIsIso
          cP.outputAugmentation cP.inputRelativeKFlat)
        (scalarKernelLocalizedDerivedSquare φ E B Q cQ.augmentationIsIso
          cQ.outputAugmentation cQ.inputRelativeKFlat)).hom ≫
        Functor.whiskerLeft (derivedExtension φ D)
          (kernelCompositionIso A' (DGBaseChange φ D) (DGBaseChange φ E) (DGBaseChange φ B) hD'
            ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
            ((scalarKernelDerivedExtension φ E B).obj ((bimoduleToDerived A B E).obj Q))).hom := by
  simp only [scalarKernelLocalizedCompositionSquare, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← Category.assoc, ← Category.assoc, ← Functor.whiskerRight_comp, Iso.hom_inv_id]
  simp only [Functor.whiskerRight_id', Category.id_comp]

/-- 実際の合成kernelの係数変更作用図式を、両側のPerfへ制限する。 -/
def scalarKernelLocalizedCompositionPerfectSquare
    (hP : kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P))
    (hQ : kernelColumnsPerfect A E B ((bimoduleToDerived A B E).obj Q)) :=
  scalarPerfectSquare φ D B _ _
    (fun _ h => perfectDerivedKernelAction_preserves A D B _
      (kernelCompose_columnsPerfect_of_columns A D E B hD _ _ hP hQ) h)
    (fun _ h => perfectDerivedKernelAction_preserves A' (DGBaseChange φ D) (DGBaseChange φ B) _
      (kernelCompose_columnsPerfect_of_columns A' (DGBaseChange φ D) (DGBaseChange φ E)
        (DGBaseChange φ B) hD' _ _
        (scalarKernelLocalized_columnsPerfect φ D E P cP.augmentationIsIso
          cP.outputAugmentation cP.inputRelativeKFlat hP)
        (scalarKernelLocalized_columnsPerfect φ E B Q cQ.augmentationIsIso
          cQ.outputAugmentation cQ.inputRelativeKFlat hQ)) h)
    (scalarKernelLocalizedCompositionSquare φ D E B hD hD' P Q cP cQ)

lemma scalarKernelLocalizedCompositionPerfectSquare_inclusion
    (hP : kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P))
    (hQ : kernelColumnsPerfect A E B ((bimoduleToDerived A B E).obj Q)) :
    Functor.whiskerRight
        (scalarKernelLocalizedCompositionPerfectSquare φ D E B hD hD' P Q cP cQ hP hQ).hom
        (perfectModuleInclusion A' (DGBaseChange φ B) Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ)
        (scalarKernelLocalizedCompositionSquare φ D E B hD hD' P Q cP cQ).hom := rfl

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelLocalizedComposition

/-! ## ScalarExtensionOutputEvaluation（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionOutputEvaluation.lean） -/

/-! # 出力加群と出力複体の導来係数変更をつなぐ計算モデル

評価した複体のK-flat性と、加群係数変更の増大の可逆性を分けて保持する。
指定モデルを持つ導来対象について、二つの導来係数変更の評価を実際の射で比較する。
-/

@[expose] public section ScalarExtensionOutputEvaluation
universe u v z z'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (E : Type v) [DGCategory A E] [Small.{u} E]
  [HasDerivedCategory.{z} (ModuleCat.{u} A)]
  [HasDerivedCategory.{z'} (ModuleCat.{u} A')]

/-- 加群側の係数変更の評価から、通常係数変更の評価への自然な増大。 -/
def scalarOutputModuleEvaluationAugmentation (e : E) :
    moduleToDerived A E ⋙ derivedExtension φ E ⋙
        moduleDerivedEvaluation A' (DGBaseChange φ E) e ⟶
      moduleEvaluation A E e ⋙ extension φ ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (derivedExtensionAugmentation φ E)
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e) ≫
    (Functor.isoWhiskerLeft (moduleExtension φ E)
      (eqToIso (moduleDerivedEvaluation_fac A' (DGBaseChange φ E) e))).hom ≫
    (Functor.isoWhiskerRight (moduleExtensionEvaluationIso φ E e) DerivedCategory.Q).hom

/-- 複体側の係数変更から同じ通常評価モデルへの自然な増大。 -/
def scalarOutputComplexEvaluationAugmentation (e : E) :
    moduleToDerived A E ⋙ moduleDerivedEvaluation A E e ⋙ complexDerivedExtension φ ⟶
      moduleEvaluation A E e ⋙ extension φ ⋙ DerivedCategory.Q :=
  (Functor.isoWhiskerRight (eqToIso (moduleDerivedEvaluation_fac A E e))
      (complexDerivedExtension φ)).hom ≫
    Functor.whiskerLeft (moduleEvaluation A E e) (complexDerivedExtensionAugmentation φ)

omit [HasDerivedCategory (ModuleCat.{u} A)] in
lemma scalarOutputModuleEvaluationAugmentation_isIso (e : E) (N : ModuleCategory A E)
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N)) :
    IsIso ((scalarOutputModuleEvaluationAugmentation φ E e).app N) := by
  let := hAug
  dsimp only [scalarOutputModuleEvaluationAugmentation, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom]
  infer_instance

lemma scalarOutputComplexEvaluationAugmentation_isIso (e : E) (N : ModuleCategory A E)
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N)) :
    IsIso ((scalarOutputComplexEvaluationAugmentation φ E e).app N) := by
  have := complexDerivedExtensionAugmentation_isIso φ ((moduleEvaluation A E e).obj N) hN
  dsimp only [scalarOutputComplexEvaluationAugmentation, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- モデルの増大を反転し、出力加群の係数変更と評価複体の係数変更を比較する。 -/
def scalarOutputEvaluationModelIso (e : E) (N : ModuleCategory A E)
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N)) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj ((moduleToDerived A E).obj N)) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj
        ((derivedExtension φ E).obj ((moduleToDerived A E).obj N)) := by
  have := scalarOutputModuleEvaluationAugmentation_isIso φ E e N hAug
  have := scalarOutputComplexEvaluationAugmentation_isIso φ E e N hN
  exact asIso ((scalarOutputComplexEvaluationAugmentation φ E e).app N) ≪≫
    (asIso ((scalarOutputModuleEvaluationAugmentation φ E e).app N)).symm

/-- 比較は、加群と複体の実際の二つの増大を可換にする。 -/
lemma scalarOutputEvaluationModelIso_augmentation (e : E) (N : ModuleCategory A E)
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N)) :
    (scalarOutputEvaluationModelIso φ E e N hN hAug).hom ≫
        (scalarOutputModuleEvaluationAugmentation φ E e).app N =
      (scalarOutputComplexEvaluationAugmentation φ E e).app N := by
  have := scalarOutputModuleEvaluationAugmentation_isIso φ E e N hAug
  simp only [scalarOutputEvaluationModelIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- 条件を満たす出力モデル間の全閉零射についての自然性。 -/
lemma scalarOutputEvaluationModelIso_naturality (e : E) {N N' : ModuleCategory A E}
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N))
    (hN' : complexKFlat A ((moduleEvaluation A E e).obj N'))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N))
    (hAug' : IsIso ((derivedExtensionAugmentation φ E).app N')) (f : N ⟶ N') :
    (complexDerivedExtension φ).map
        ((moduleDerivedEvaluation A E e).map ((moduleToDerived A E).map f)) ≫
        (scalarOutputEvaluationModelIso φ E e N' hN' hAug').hom =
      (scalarOutputEvaluationModelIso φ E e N hN hAug).hom ≫
        (moduleDerivedEvaluation A' (DGBaseChange φ E) e).map
          ((derivedExtension φ E).map ((moduleToDerived A E).map f)) := by
  let β := scalarOutputModuleEvaluationAugmentation φ E e
  let γ := scalarOutputComplexEvaluationAugmentation φ E e
  have : IsIso (β.app N') := by
    let := hAug'
    dsimp only [β, scalarOutputModuleEvaluationAugmentation, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom]
    infer_instance
  apply (cancel_mono (β.app N')).1
  rw [Category.assoc, scalarOutputEvaluationModelIso_augmentation]
  have hn := β.naturality f
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  erw [hn]
  rw [← Category.assoc, scalarOutputEvaluationModelIso_augmentation]
  exact γ.naturality f

/-- 出力dg圏の局所Hom K-flat性とモデルの各値のK-flat性による十分条件版。 -/
def scalarOutputEvaluationModelIso_ofObjectwiseKFlat
    (hE : localHomKFlat A E) (N : ModuleCategory A E)
    (hN : moduleObjectwiseKFlat A E (ForgetEnrichment.to (Complex A) N)) (e : E) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj ((moduleToDerived A E).obj N)) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj
        ((derivedExtension φ E).obj ((moduleToDerived A E).obj N)) :=
  scalarOutputEvaluationModelIso φ E e N (hN e)
    (derivedExtensionAugmentation_isIso_of_objectwiseKFlat φ E N hE hN)

/-- 指定された計算モデルを持つ任意の主導来出力に、実際の比較を移す。 -/
def scalarOutputEvaluationIso (e : E) (X : DerivedModuleCategory A E)
    (N : ModuleCategory A E) (i : X ≅ (moduleToDerived A E).obj N)
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N)) :
    (complexDerivedExtension φ).obj ((moduleDerivedEvaluation A E e).obj X) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj ((derivedExtension φ E).obj X) :=
  (complexDerivedExtension φ).mapIso ((moduleDerivedEvaluation A E e).mapIso i) ≪≫
    scalarOutputEvaluationModelIso φ E e N hN hAug ≪≫
    (derivedExtension φ E ⋙ moduleDerivedEvaluation A' (DGBaseChange φ E) e).mapIso i.symm

/-- モデルへの移送と評価比較の正方形。 -/
lemma scalarOutputEvaluationIso_model (e : E) (X : DerivedModuleCategory A E)
    (N : ModuleCategory A E) (i : X ≅ (moduleToDerived A E).obj N)
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N)) :
    (scalarOutputEvaluationIso φ E e X N i hN hAug).hom ≫
        (moduleDerivedEvaluation A' (DGBaseChange φ E) e).map ((derivedExtension φ E).map i.hom) =
      (complexDerivedExtension φ).map ((moduleDerivedEvaluation A E e).map i.hom) ≫
        (scalarOutputEvaluationModelIso φ E e N hN hAug).hom := by
  simp only [scalarOutputEvaluationIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.comp_map, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionOutputEvaluation

/-! ## ScalarExtensionKernelOutputEvaluation（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelOutputEvaluation.lean） -/

/-! # kernel出力の導来係数変更と評価の比較

標準右解像度tensorを出力の計算モデルに使う。
U12fの入力と全dg加群正方形の入力を、増大とK-flat計算から独立に比較する。
-/

@[expose] public section ScalarExtensionKernelOutputEvaluation
universe u v w z z'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  [HasDerivedCategory.{z} (ModuleCat.{u} A)]
  [HasDerivedCategory.{z'} (ModuleCat.{u} A')]

/-- kernel出力を標準右解像度tensorで計算して、二つの導来係数変更を比較する。 -/
def scalarKernelOutputEvaluationIso (e : E) (M : ModuleCategory A D)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
      (P.leftAt e)))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj))) :
    (complexDerivedExtension φ).obj ((moduleDerivedEvaluation A E e).obj
        ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M))) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj ((derivedExtension φ E).obj
        ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M))) :=
  scalarOutputEvaluationIso φ E e _ _
    (kernelResolutionDerivedTensorComputation A D E P (moduleCanonicalProjectiveResolution A D) M)
    hPN hAug

/-- 出力dg圏の局所Hom K-flat性と全評価でのhPNによる比較。 -/
def scalarKernelOutputEvaluationIso_ofKFlatModels
    (hE : localHomKFlat A E) (M : ModuleCategory A D)
    (hPN : ∀ e : E, complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
      (P.leftAt e))) (e : E) :
    (complexDerivedExtension φ).obj ((moduleDerivedEvaluation A E e).obj
        ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M))) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj ((derivedExtension φ E).obj
        ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M))) :=
  scalarKernelOutputEvaluationIso φ D E P e M (hPN e)
    (derivedExtensionAugmentation_isIso_of_objectwiseKFlat φ E
      ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj) hE hPN)

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelOutputEvaluation
