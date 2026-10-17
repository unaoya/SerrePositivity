module
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelImage
public import SerrePositivity.DifferentialGraded.Derived.RightTensor
public import SerrePositivity.DifferentialGraded.Derived.EvaluationTriangles
public import SerrePositivity.DifferentialGraded.Tensor.Homotopy

/-! # 実際のkernel導来作用の評価とU12d導来tensorの自然比較

U14の評価比較と同じ既存のH⁰・主局所化計算を、任意kernelへ適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

lemma perfectKernelTensor_map_π (M N : RightModule A D) (e : E) :
    (kernelTensor A D E P).map M N ≫
      moduleHomπ A E ((kernelTensor A D E P).obj M) ((kernelTensor A D E P).obj N) e =
        BalancedTensor.rightHomMap A D M N (P.leftAt e) := by
  have h := BimoduleTensor.compose_leftMap_π A E D (RightModule A D) P
    (DGFunctor.id (RightModule A D)) M N e
  exact h.trans (Category.id_comp _)

lemma perfectKernelTensor_map_eval {M N : ModuleCategory A D} (f : M ⟶ N) (e : E) :
    (moduleEvaluation A E e).map ((kernelTensor A D E P).onClosed.map f) =
      BalancedTensor.rightTensorMap A D (P.leftAt e) f := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain]
  change (moduleHomπ A E _ _ e).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
      (kernelTensor A D E P).map _ _)).val = _
  rw [cycleFromUnit_postcomp]
  have h := congrArg (fun k => k.f 0 (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex A) f)).val)
      (perfectKernelTensor_map_π A D E P
        (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) e)
  exact h.trans (BalancedTensor.rightHomMap_closedElement A D (P.leftAt e) f)

def perfectKernelTensorEvaluationIso (d : E) :
    (kernelTensor A D E P).onClosed ⋙ moduleEvaluation A E d ≅
      BalancedTensor.rightTensorFunctor A D
        (P.leftAt d) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change (moduleEvaluation A E d).map ((kernelTensor A D E P).onClosed.map f) ≫ 𝟙 _ =
      𝟙 _ ≫ BalancedTensor.rightTensorMap A D
        (P.leftAt d) f
    rw [Category.comp_id, Category.id_comp]
    exact perfectKernelTensor_map_eval A D E P f d)

variable [HasDerivedCategory.{z} (ModuleCat.{u} A)]

/-- K(D)上のkernel作用評価を、閉零代表上でbalanced tensorと比較する。 -/
def perfectKernelTensorHomotopyEvaluationFacIso (d : E) :
    moduleToHomotopy A D ⋙
        (kernelTensor A D E P).onHomotopy ⋙
          moduleHomotopyToDerivedClosed A E ⋙ moduleDerivedEvaluation A E d ≅
      BalancedTensor.rightTensorFunctor A D
        (P.leftAt d) ⋙ DerivedCategory.Q :=
  (Functor.associator (moduleToHomotopy A D)
    (kernelTensor A D E P).onHomotopy
    (moduleHomotopyToDerivedClosed A E ⋙ moduleDerivedEvaluation A E d)).symm ≪≫
  Functor.isoWhiskerRight (eqToIso (kernelTensor A D E P).onHomotopy_fac)
    (moduleHomotopyToDerivedClosed A E ⋙ moduleDerivedEvaluation A E d) ≪≫
  Functor.associator (kernelTensor A D E P).onClosed (moduleToHomotopy A E)
    (moduleHomotopyToDerivedClosed A E ⋙ moduleDerivedEvaluation A E d) ≪≫
  Functor.isoWhiskerLeft (kernelTensor A D E P).onClosed
    ((Functor.associator (moduleToHomotopy A E) (moduleHomotopyToDerivedClosed A E)
      (moduleDerivedEvaluation A E d)).symm ≪≫ moduleDerivedEvaluationHomotopyFacIso A E d) ≪≫
  (Functor.associator (kernelTensor A D E P).onClosed (moduleEvaluation A E d)
    DerivedCategory.Q).symm ≪≫
  Functor.isoWhiskerRight (perfectKernelTensorEvaluationIso A D E P d) DerivedCategory.Q

/-- U12dのhomotopy tensorを、閉零代表上で同じbalanced tensorへ比較する。 -/
def perfectKernelU12dHomotopyTensorFacIso (d : E) :
    moduleToHomotopy A D ⋙
        BalancedTensor.rightTensorHomotopyFunctor A D
          (P.leftAt d) ⋙ DerivedCategory.Qh ≅
      BalancedTensor.rightTensorFunctor A D
        (P.leftAt d) ⋙ DerivedCategory.Q :=
  (Functor.associator (moduleToHomotopy A D)
    (BalancedTensor.rightTensorHomotopyFunctor A D
      (P.leftAt d)) DerivedCategory.Qh).symm ≪≫
  Functor.isoWhiskerRight
    (eqToIso (BalancedTensor.rightTensorHomotopyFunctor_fac A D
      (P.leftAt d))) DerivedCategory.Qh ≪≫
  Functor.associator
    (BalancedTensor.rightTensorFunctor A D
      (P.leftAt d))
    (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)) DerivedCategory.Qh ≪≫
  Functor.isoWhiskerLeft
    (BalancedTensor.rightTensorFunctor A D
      (P.leftAt d))
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))

/-- 全てのK(D)射に自然な、kernel作用評価とU12dの比較。 -/
def perfectKernelTensorHomotopyEvaluationIso (d : E) :
    (kernelTensor A D E P).onHomotopy ⋙
        moduleHomotopyToDerivedClosed A E ⋙ moduleDerivedEvaluation A E d ≅
      BalancedTensor.rightTensorHomotopyFunctor A D
        (P.leftAt d) ⋙ DerivedCategory.Qh :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    (perfectKernelTensorHomotopyEvaluationFacIso A D E P d ≪≫
      (perfectKernelU12dHomotopyTensorFacIso A D E P d).symm)

/-- 任意の右射影解像度族について、導来tensorのE評価はU12dの導来tensorと自然同型。 -/
def perfectKernelResolutionDerivedTensorEvaluationIso
    (R : ∀ N : ModuleCategory A D,
      ModuleProjectiveResolution A D N) (d : E) :
    kernelResolutionDerivedTensor A D E P R ⋙ moduleDerivedEvaluation A E d ≅
      moduleResolutionDerivedTensor A D R
        (P.leftAt d) :=
  Functor.associator (moduleDerivedResolutionFunctor A D R)
    ((kernelTensor A D E P).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E)
    (moduleDerivedEvaluation A E d) ≪≫
  Functor.isoWhiskerLeft (moduleDerivedResolutionFunctor A D R)
    (Functor.associator (kernelTensor A D E P).onHomotopy
      (moduleHomotopyToDerivedClosed A E) (moduleDerivedEvaluation A E d) ≪≫
        perfectKernelTensorHomotopyEvaluationIso A D E P d)

/-- 主kernel導来作用と既存U12d導来tensorの自然な評価正方形。 -/
def perfectKernelDerivedTensorEvaluationIso (d : E) :
    kernelDerivedTensorOnBimodule A D E P ⋙ moduleDerivedEvaluation A E d ≅
      moduleDerivedTensorRight A D
        (P.leftAt d) :=
  perfectKernelResolutionDerivedTensorEvaluationIso A D E P
    (moduleCanonicalProjectiveResolution A D) d
def perfectKernelActionEvaluationIso
    (hP : ∀ x : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt x)))) (e : E) :
    perfectKernelAction A D E P hP ⋙ perfectModuleInclusion A E Set.univ ⋙
        moduleDerivedEvaluation A E e ≅
      perfectModuleInclusion A D Set.univ ⋙ moduleDerivedTensorRight A D (P.leftAt e) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectKernelActionInclusionIso A D E P hP) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (perfectKernelDerivedTensorEvaluationIso A D E P e)

end SerrePositivity.DifferentialGraded.Morita
