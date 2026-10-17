module
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelEvaluation
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionTensorModels

/-! # 実際のkernel導来作用とU12f係数変更の評価正方形

各出力評価eで実際の作用をU12d tensorへ自然に比較し、U12fのhPN・hP'をそのまま用いる。
核変数の局所化・核合成の比較をこのファイルの結論へ混ぜない。
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

/-- 全ての主導来入力射に自然な、係数変更後のkernel作用評価。 -/
def scalarKernelTensorEvaluationIso (e : E) :
    kernelDerivedTensorOnBimodule A D E P ⋙ moduleDerivedEvaluation A E e ⋙
        complexDerivedExtension φ ≅
      moduleDerivedTensorRight A D (P.leftAt e) ⋙ complexDerivedExtension φ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectKernelDerivedTensorEvaluationIso A D E P e) _

lemma scalarKernelTensorEvaluationIso_app (e : E) (X : DerivedModuleCategory A D) :
    (scalarKernelTensorEvaluationIso φ D E P e).hom.app X =
      (complexDerivedExtension φ).map
        ((perfectKernelDerivedTensorEvaluationIso A D E P e).hom.app X) := by
  simp only [scalarKernelTensorEvaluationIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp]

def scalarKernelTensorBaseChange (e : E) {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (P.leftAt e)))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) R.obj))) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj
          ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M))) ≅
      (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D (P.leftAt e))).obj
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) :=
  (complexDerivedExtension φ).mapIso
      ((perfectKernelDerivedTensorEvaluationIso A D E P e).app ((moduleToDerived A D).obj M)) ≪≫
    derivedTensorBaseChange φ D R (P.leftAt e) hPN hP'

variable (hP : ∀ x : D, modulePerfect A E ((moduleToDerived A E).obj
  (ForgetEnrichment.of (Complex A) (P.rightAt x))))

def scalarPerfectKernelTensorEvaluationIso (e : E) :
    (perfectKernelAction A D E P hP ⋙ perfectModuleInclusion A E Set.univ ⋙
        moduleDerivedEvaluation A E e) ⋙ complexDerivedExtension φ ≅
      perfectModuleInclusion A D Set.univ ⋙ moduleDerivedTensorRight A D (P.leftAt e) ⋙
        complexDerivedExtension φ :=
  Functor.isoWhiskerRight (perfectKernelActionEvaluationIso A D E P hP e) _ ≪≫
    Functor.associator _ _ _

def scalarPerfectKernelTensorBaseChange (e : E) {M : ModuleCategory A D}
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
      (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D (P.leftAt e))).obj
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) :=
  scalarKernelTensorBaseChange φ D E P e R hPN hP'

end SerrePositivity.DifferentialGraded.Morita
