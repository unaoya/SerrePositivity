module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionOutputEvaluation
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelAction

/-! # kernel出力の導来係数変更と評価の比較

標準右解像度tensorを出力の計算モデルに使う。
U12fの入力と全dg加群正方形の入力を、増大とK-flat計算から独立に比較する。
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
