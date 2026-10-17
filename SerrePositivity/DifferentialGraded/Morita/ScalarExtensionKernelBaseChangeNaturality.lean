module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelFunctor
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionTensorNaturality
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelEvaluationNaturality

/-! # kernel射に自然な、実際の作用評価のU12f係数変更比較

指定右解像度についてhPN・hP'を満たすkernelの充満部分圏上で自然同型を構成する。
始域は出力評価の複体の導来係数変更であり、出力dg加群の係数変更との交換は含めない。
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
