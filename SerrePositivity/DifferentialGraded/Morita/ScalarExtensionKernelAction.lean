module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernel
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelTensor

/-! # 係数変更した実際のkernel作用へのU12f評価比較

U12fの終域tensorを係数変更したkernelの主導来作用の評価と同定する。
sourceは複体の導来係数変更であり、dg加群の導来係数変更と評価の交換を無条件には仮定しない。
-/
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
  [HasDerivedCategory.{z} (ModuleCat.{u} A)] [HasDerivedCategory.{z'} (ModuleCat.{u} A')]

def scalarKernelActionBaseChange (e : E) {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (P.leftAt e)))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) R.obj))) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj
          ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M))) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj
        ((kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).obj ((derivedExtension φ D).obj ((moduleToDerived A D).obj M))) :=
  scalarKernelTensorBaseChange φ D E P e R hPN hP' ≪≫ (by
    rw [← scalarKernel_leftAt φ D E P e]
    exact ((perfectKernelDerivedTensorEvaluationIso A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P) e).app
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M))).symm)

def scalarPerfectKernelActionBaseChange
    (hP : ∀ x : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt x))))
    (e : E) {M : ModuleCategory A D}
    (hM : modulePerfect A D ((moduleToDerived A D).obj M))
    (R : ModuleProjectiveResolution A D M)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (P.leftAt e)))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) R.obj))) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj
          ((perfectModuleInclusion A E Set.univ).obj
            ((perfectKernelAction A D E P hP).obj ⟨_, hM⟩))) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj
        ((kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).obj ((derivedExtension φ D).obj ((moduleToDerived A D).obj M))) :=
  scalarKernelActionBaseChange φ D E P e R hPN hP'

end SerrePositivity.DifferentialGraded.Morita
