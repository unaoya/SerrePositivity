module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelBalancedModule
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.LeftNaturality

/-! # kernel作用のunderived係数変更の入力自然性 -/
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

lemma scalarKernelBalancedValueIso_right_naturality
    {M N : ModuleCategory A D} (f : M ⟶ N) (e : E) :
    (extension φ).map ((BalancedTensor.rightTensorFunctor A D (P.leftAt e)).map f) ≫
        (scalarKernelBalancedValueIso φ D E P (ForgetEnrichment.to (Complex A) N) e).hom =
      (scalarKernelBalancedValueIso φ D E P (ForgetEnrichment.to (Complex A) M) e).hom ≫
        (BalancedTensor.rightTensorFunctor A' (DGBaseChange φ D)
          ((scalarKernel φ D E P).leftAt e)).map ((moduleExtension φ D).map f) := by
  have hb := balancedIso_module_naturality φ D f
    (𝟙 (ForgetEnrichment.of (Complex A) (P.leftAt e)))
  simp only [CategoryTheory.Functor.map_id] at hb
  have hn := (BalancedTensor.rightTensorLeftMap A' (DGBaseChange φ D)
    (scalarKernelLeftValueIso φ D E P e).inv).naturality ((moduleExtension φ D).map f)
  simp only [scalarKernelBalancedValueIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Category.assoc]
  erw [hb]
  rw [Category.assoc, Category.assoc]
  congr 1

lemma scalarKernelBalancedIso_right_naturality
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleExtension φ E).map ((kernelTensor A D E P).onClosed.map f) ≫
        (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) N)).hom =
      (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M)).hom ≫
        (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).onClosed.map ((moduleExtension φ D).map f) := by
  apply moduleMorphism_ext
  intro e
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleExtension_eval, scalarKernelBalancedIso_hom_eval, scalarKernelBalancedIso_hom_eval,
    perfectKernelTensor_map_eval, perfectKernelTensor_map_eval]
  exact scalarKernelBalancedValueIso_right_naturality φ D E P f e

/-- 全閉零入力射に自然な、実際のdg加群値の係数変更比較。 -/
def scalarKernelBalancedNatIso :
    (kernelTensor A D E P).onClosed ⋙ moduleExtension φ E ≅
      moduleExtension φ D ⋙
        (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).onClosed :=
  NatIso.ofComponents
    (fun M => scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M))
    (by intro M N f; exact scalarKernelBalancedIso_right_naturality φ D E P f)

end SerrePositivity.DifferentialGraded.Morita
