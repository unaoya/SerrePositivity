module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelBalancedNaturality
public import SerrePositivity.DifferentialGraded.Morita.KernelNaturality

/-! # kernel射に関する実際のunderived係数変更比較の自然性 -/
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
  {P Q : BimoduleCategory A E D} (f : P ⟶ Q)

lemma scalarKernelLeftValueIso_kernel_naturality (e : E) :
    (leftModuleExtension φ D).map ((BimoduleCategory.leftEvaluation A E D e).map f) ≫
        (scalarKernelLeftValueIso φ D E (BimoduleCategory.underlying A E D Q) e).inv =
      (scalarKernelLeftValueIso φ D E (BimoduleCategory.underlying A E D P) e).inv ≫
        (BimoduleCategory.leftEvaluation A' (DGBaseChange φ E) (DGBaseChange φ D) e).map
          ((scalarKernelFunctor φ D E).map f) :=
by
  apply leftModuleMorphism_ext A' (DGBaseChange φ D)
  intro d
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rw [leftModuleExtension_eval, BimoduleCategory.leftEvaluation_map_eval,
    BimoduleCategory.leftEvaluation_map_eval]
  erw [scalarKernelLeftValueIso_inv_eval φ D E (BimoduleCategory.underlying A E D Q) e d,
    scalarKernelLeftValueIso_inv_eval φ D E (BimoduleCategory.underlying A E D P) e d]
  erw [Category.comp_id, Category.id_comp]
  exact (scalarKernelMap_value φ D E f e d).symm

lemma scalarKernelBalancedValueIso_kernel_naturality (M : ModuleCategory A D) (e : E) :
    (extension φ).map (BalancedTensor.map A D (𝟙 M)
        ((BimoduleCategory.leftEvaluation A E D e).map f)) ≫
        (scalarKernelBalancedValueIso φ D E (BimoduleCategory.underlying A E D Q)
          (ForgetEnrichment.to (Complex A) M) e).hom =
      (scalarKernelBalancedValueIso φ D E (BimoduleCategory.underlying A E D P)
        (ForgetEnrichment.to (Complex A) M) e).hom ≫
        BalancedTensor.map A' (DGBaseChange φ D) (𝟙 ((moduleExtension φ D).obj M))
          ((BimoduleCategory.leftEvaluation A' (DGBaseChange φ E) (DGBaseChange φ D) e).map
            ((scalarKernelFunctor φ D E).map f)) := by
  have hb := balancedIso_module_naturality φ D (𝟙 M)
    ((BimoduleCategory.leftEvaluation A E D e).map f)
  simp only [CategoryTheory.Functor.map_id] at hb
  have he := congrArg
    (BalancedTensor.leftTensorFunctor A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) M))).map
    (scalarKernelLeftValueIso_kernel_naturality φ D E f e)
  simp only [CategoryTheory.Functor.map_comp] at he
  simp only [scalarKernelBalancedValueIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Category.assoc]
  erw [hb]
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun k => (balancedIso φ D (ForgetEnrichment.to (Complex A) M)
    ((BimoduleCategory.underlying A E D P).leftAt e)).hom ≫ k) he

lemma scalarKernelBalancedIso_kernel_naturality (M : ModuleCategory A D) :
    (moduleExtension φ E).map ((kernelTensorMap A D E f).app M) ≫
        (scalarKernelBalancedIso φ D E (BimoduleCategory.underlying A E D Q)
          (ForgetEnrichment.to (Complex A) M)).hom =
      (scalarKernelBalancedIso φ D E (BimoduleCategory.underlying A E D P)
        (ForgetEnrichment.to (Complex A) M)).hom ≫
        (kernelTensorMap A' (DGBaseChange φ D) (DGBaseChange φ E)
          ((scalarKernelFunctor φ D E).map f)).app ((moduleExtension φ D).obj M) := by
  apply moduleMorphism_ext
  intro e
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleExtension_eval, scalarKernelBalancedIso_hom_eval, scalarKernelBalancedIso_hom_eval,
    kernelTensorMap_value, kernelTensorMap_value]
  exact scalarKernelBalancedValueIso_kernel_naturality φ D E f M e

/-- 入力射への自然同型は、kernelの全閉零射にも自然。 -/
lemma scalarKernelBalancedNatIso_kernel_naturality :
    Functor.whiskerRight (kernelTensorMap A D E f) (moduleExtension φ E) ≫
        (scalarKernelBalancedNatIso φ D E (BimoduleCategory.underlying A E D Q)).hom =
      (scalarKernelBalancedNatIso φ D E (BimoduleCategory.underlying A E D P)).hom ≫
        Functor.whiskerLeft (moduleExtension φ D)
          (kernelTensorMap A' (DGBaseChange φ D) (DGBaseChange φ E)
            ((scalarKernelFunctor φ D E).map f)) := by
  apply NatTrans.ext
  funext M
  exact scalarKernelBalancedIso_kernel_naturality φ D E f M

end SerrePositivity.DifferentialGraded.Morita
