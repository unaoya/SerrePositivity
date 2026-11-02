module
public import SerrePositivity.DifferentialGraded.Morita.Kernel
public import Mathlib.Tactic.CategoryTheory.Slice
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtension.PerfectSquares


/-! # kernel出力評価とU12f比較の成分計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z z'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  [HasDerivedCategory.{z} (ModuleCat.{u} A)]
  [HasDerivedCategory.{z'} (ModuleCat.{u} A')]
  (hAug : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
  (hP' : ∀ M : ModuleCategory A D,
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A)
        (moduleCanonicalProjectiveResolution A D M).obj)))

omit E P hAug hP' [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} A')] in
lemma scalarDerivedExtensionResolutionComputation_canonical (M : ModuleCategory A D) :
    derivedExtensionResolutionComputation φ D (moduleCanonicalProjectiveResolution A D M) =
      resolutionDerivedExtensionComputation φ D (moduleCanonicalProjectiveResolution A D) M := by
  apply Iso.ext
  simp only [derivedExtensionResolutionComputation, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [ModuleProjectiveResolution.comparison_self, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

omit φ E P hAug hP' [HasDerivedCategory (ModuleCat.{u} A')] in
lemma scalarTensorResolutionComputation_canonical (M : ModuleCategory A D) (N : LeftModule A D) :
    moduleDerivedTensorRightResolutionComputation A D (moduleCanonicalProjectiveResolution A D M) N =
      moduleResolutionDerivedTensorComputation A D (moduleCanonicalProjectiveResolution A D) N M := by
  rw [moduleDerivedTensorRightResolutionComputation, moduleProjectiveResolutionTensorIso_self]
  exact Iso.trans_refl _

lemma scalarKernelTensorBaseChange_computation (e : E) (M : ModuleCategory A D)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
      (P.leftAt e)))
    (hInput : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A)
        (moduleCanonicalProjectiveResolution A D M).obj))) :
    (scalarKernelTensorBaseChange φ D E P e (moduleCanonicalProjectiveResolution A D M)
        hPN hInput).hom ≫
      (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D (P.leftAt e))).map
        (resolutionDerivedExtensionComputation φ D (moduleCanonicalProjectiveResolution A D) M).hom ≫
      (relativeKFlatTensorComputation (DGBaseChange φ D)
        ((moduleExtension φ D).obj (moduleCanonicalProjectiveResolution A D M).obj)
        hInput (leftModule φ D (P.leftAt e))).hom =
    (complexDerivedExtension φ).map ((moduleDerivedEvaluation A E e).map
      (kernelResolutionDerivedTensorComputation A D E P (moduleCanonicalProjectiveResolution A D) M).hom) ≫
    (complexDerivedExtension φ).map ((eqToIso (moduleDerivedEvaluation_fac A E e)).hom.app
      ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)) ≫
    (complexDerivedExtensionKFlatIso φ _ hPN).hom ≫
    DerivedCategory.Q.map (balancedIso φ D
      (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj) (P.leftAt e)).hom := by
  simp only [scalarKernelTensorBaseChange, derivedTensorBaseChange,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [scalarDerivedExtensionResolutionComputation_canonical,
    scalarTensorResolutionComputation_canonical]
  erw [← CategoryTheory.Functor.map_comp_assoc
    (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D (P.leftAt e))),
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.inv_hom_id, Category.comp_id]
  have hs := scalarKernelResolutionEvaluation_computation A D E P
    (moduleCanonicalProjectiveResolution A D) e M
  erw [← CategoryTheory.Functor.map_comp_assoc (complexDerivedExtension φ), ← hs]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

omit φ hAug hP' [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} A')] in
lemma scalarKernelEvaluation_value (M : ModuleCategory A D) (e : E) :
    (moduleEvaluation A E e).obj ((kernelTensor A D E P).onClosed.obj M) =
      BalancedTensor.obj A D (ForgetEnrichment.to (Complex A) M) (P.leftAt e) := rfl

/-- 出力評価比較を挿入した通常モデルのbalanced図式。 -/
lemma scalarKernelOutputEvaluationModelIso_balanced (e : E) (M : ModuleCategory A D)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) M) (P.leftAt e)))
    (hOutput : IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E P).onClosed.obj M))) :
    (scalarOutputEvaluationModelIso φ E e ((kernelTensor A D E P).onClosed.obj M)
        hPN hOutput).hom ≫
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).map
        ((derivedExtensionAugmentation φ E).app ((kernelTensor A D E P).onClosed.obj M)) ≫
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).map
        ((moduleToDerived A' (DGBaseChange φ E)).map
          (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M)).hom) ≫
      (eqToIso (moduleDerivedEvaluation_fac A' (DGBaseChange φ E) e)).hom.app
        ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).onClosed.obj
          ((moduleExtension φ D).obj M)) =
    (complexDerivedExtension φ).map ((eqToIso (moduleDerivedEvaluation_fac A E e)).hom.app
      ((kernelTensor A D E P).onClosed.obj M)) ≫
      (complexDerivedExtensionKFlatIso φ _ hPN).hom ≫
      DerivedCategory.Q.map
        (scalarKernelBalancedValueIso φ D E P (ForgetEnrichment.to (Complex A) M) e).hom := by
  have hf := (eqToIso (moduleDerivedEvaluation_fac A' (DGBaseChange φ E) e)).hom.naturality
    (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M)).hom
  change (moduleDerivedEvaluation A' (DGBaseChange φ E) e).map
    ((moduleToDerived A' (DGBaseChange φ E)).map
      (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M)).hom) ≫ _ =
    _ ≫ DerivedCategory.Q.map ((moduleEvaluation A' (DGBaseChange φ E) e).map
      (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M)).hom) at hf
  erw [hf]
  rw [scalarKernelBalancedIso_hom_eval]
  have ha := scalarOutputEvaluationModelIso_augmentation φ E e
    ((kernelTensor A D E P).onClosed.obj M) hPN hOutput
  simp only [scalarOutputModuleEvaluationAugmentation, scalarOutputComplexEvaluationAugmentation,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    moduleExtensionEvaluationIso, NatIso.ofComponents, Iso.refl_hom,
    CategoryTheory.Functor.map_id, Category.comp_id] at ha
  erw [Category.comp_id] at ha
  simpa only [moduleEvaluationToDerived, Functor.comp_obj, scalarKernelEvaluation_value,
    moduleExtension, ForgetEnrichment.to_of,
    Category.assoc, complexDerivedExtensionKFlatIso, asIso_hom] using
    congrArg (fun k => k ≫ DerivedCategory.Q.map
      (scalarKernelBalancedValueIso φ D E P (ForgetEnrichment.to (Complex A) M) e).hom) ha

/-- 出力評価比較を挿入した全dg加群正方形は、既存U12fの評価比較と一致する。 -/
lemma scalarKernelOutputEvaluationIso_u12f (e : E) (M : ModuleCategory A D)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
      (P.leftAt e))) :
    (scalarKernelOutputEvaluationIso φ D E P e M hPN (hAug M)).hom ≫
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).map
        ((scalarKernelDerivedBaseChangeIso φ D E P hAug hP').hom.app
          ((moduleToDerived A D).obj M)) ≫
      (perfectKernelDerivedTensorEvaluationIso A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P) e).hom.app
          ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) ≫
      ((moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
        (scalarKernelLeftValueIso φ D E P e).hom).app
          ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) =
    (scalarKernelTensorBaseChange φ D E P e (moduleCanonicalProjectiveResolution A D M)
      hPN (hP' M)).hom := by
  let R := moduleCanonicalProjectiveResolution A D M
  let V := moduleDerivedEvaluation A' (DGBaseChange φ E) (show DGBaseChange φ E from e)
  let t := resolutionDerivedExtensionComputation φ D (moduleCanonicalProjectiveResolution A D) M
  let η := (moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
    (scalarKernelLeftValueIso φ D E P e).hom
  let α := perfectKernelDerivedTensorEvaluationIso A' (DGBaseChange φ D) (DGBaseChange φ E)
    (scalarKernel φ D E P) e
  let r := relativeKFlatTensorComputation (DGBaseChange φ D) ((moduleExtension φ D).obj R.obj)
    (hP' M) (leftModule φ D (P.leftAt e))
  apply (cancel_mono
    ((moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D (P.leftAt e))).map t.hom ≫
      r.hom)).1
  simp only [Category.assoc]
  erw [scalarKernelTensorBaseChange_computation φ D E P e M hPN (hP' M)]
  slice_lhs 4 5 => erw [← η.naturality t.hom]
  have hα := α.hom.naturality t.hom
  simp only [Functor.comp_map] at hα
  slice_lhs 3 4 => erw [← hα]
  slice_lhs 5 6 => erw [relativeTensorComputation_left_naturality A'
    (DGBaseChange φ D) ((moduleExtension φ D).obj R.obj) (hP' M)
    (scalarKernelLeftValueIso φ D E P e).hom]
  slice_lhs 4 5 => erw [← scalarKernelEvaluationAugmentation_relativeKFlat A'
    (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P) e
    ((moduleExtension φ D).obj R.obj) (hP' M)]
  slice_lhs 3 4 =>
    rw [← CategoryTheory.Functor.map_comp, ← scalarKernelOutputRight_model φ D E P M,
      CategoryTheory.Functor.map_comp]
  have hb := NatTrans.congr_app
    (scalarKernelDerivedBaseChangeIso_hom_comp_right φ D E P hAug hP')
    ((moduleToDerived A D).obj M)
  simp only [NatTrans.comp_app] at hb
  slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp, hb]
  slice_lhs 2 3 =>
    rw [← CategoryTheory.Functor.map_comp, scalarKernelOutputLeft_model,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  have hi := scalarOutputEvaluationIso_model φ E e _ _
    (kernelResolutionDerivedTensorComputation A D E P (moduleCanonicalProjectiveResolution A D) M)
    hPN (hAug M)
  slice_lhs 1 2 => erw [hi]
  slice_lhs 2 5 => erw [scalarKernelOutputEvaluationModelIso_balanced φ D E P e R.obj hPN (hAug M)]
  simp only [scalarKernelBalancedValueIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    CategoryTheory.Functor.map_comp, Category.assoc]
  change _ = _
  simp only [BalancedTensor.leftTensorFunctor]
  rw [← CategoryTheory.Functor.map_comp, ← BalancedTensor.map_comp, Iso.inv_hom_id,
    Category.id_comp, BalancedTensor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

end SerrePositivity.DifferentialGraded.Morita
