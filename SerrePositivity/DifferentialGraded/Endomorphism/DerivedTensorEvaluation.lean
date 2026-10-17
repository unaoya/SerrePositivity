module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensor
public import SerrePositivity.DifferentialGraded.Derived.RightTensor
public import SerrePositivity.DifferentialGraded.Derived.EvaluationTriangles

/-! # 再構成導来tensorの各D成分とU12dの導来tensorの自然比較

関手間の自然同型として比較し、対象での計算だけには留めない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 再構成tensorの各D成分はU11のbalanced tensor関手と自然に一致する。 -/
def endomorphismTensorEvaluationIso (d : D) :
    (endomorphismModuleTensor A D E).onClosed ⋙ moduleEvaluation A D d ≅
      BalancedTensor.rightTensorFunctor A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change (moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map f) ≫ 𝟙 _ =
      𝟙 _ ≫ BalancedTensor.rightTensorMap A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) f
    rw [Category.comp_id, Category.id_comp]
    exact endomorphismModuleTensor_map_eval A D E f d)

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- K(End(E))上の再構成tensor評価を、閉零代表上でbalanced tensorと比較する。 -/
def endomorphismTensorHomotopyEvaluationFacIso (d : D) :
    moduleToHomotopy A (EndomorphismObject E) ⋙
        (endomorphismModuleTensor A D E).onHomotopy ⋙
          moduleHomotopyToDerivedClosed A D ⋙ moduleDerivedEvaluation A D d ≅
      BalancedTensor.rightTensorFunctor A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) ⋙ DerivedCategory.Q :=
  (Functor.associator (moduleToHomotopy A (EndomorphismObject E))
    (endomorphismModuleTensor A D E).onHomotopy
    (moduleHomotopyToDerivedClosed A D ⋙ moduleDerivedEvaluation A D d)).symm ≪≫
  Functor.isoWhiskerRight (eqToIso (endomorphismModuleTensor A D E).onHomotopy_fac)
    (moduleHomotopyToDerivedClosed A D ⋙ moduleDerivedEvaluation A D d) ≪≫
  Functor.associator (endomorphismModuleTensor A D E).onClosed (moduleToHomotopy A D)
    (moduleHomotopyToDerivedClosed A D ⋙ moduleDerivedEvaluation A D d) ≪≫
  Functor.isoWhiskerLeft (endomorphismModuleTensor A D E).onClosed
    ((Functor.associator (moduleToHomotopy A D) (moduleHomotopyToDerivedClosed A D)
      (moduleDerivedEvaluation A D d)).symm ≪≫ moduleDerivedEvaluationHomotopyFacIso A D d) ≪≫
  (Functor.associator (endomorphismModuleTensor A D E).onClosed (moduleEvaluation A D d)
    DerivedCategory.Q).symm ≪≫
  Functor.isoWhiskerRight (endomorphismTensorEvaluationIso A D E d) DerivedCategory.Q

/-- U12dのhomotopy tensorを、閉零代表上で同じbalanced tensorへ比較する。 -/
def endomorphismU12dHomotopyTensorFacIso (d : D) :
    moduleToHomotopy A (EndomorphismObject E) ⋙
        BalancedTensor.rightTensorHomotopyFunctor A (EndomorphismObject E)
          ((endomorphismModuleAction A D E).leftAt d) ⋙ DerivedCategory.Qh ≅
      BalancedTensor.rightTensorFunctor A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) ⋙ DerivedCategory.Q :=
  (Functor.associator (moduleToHomotopy A (EndomorphismObject E))
    (BalancedTensor.rightTensorHomotopyFunctor A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt d)) DerivedCategory.Qh).symm ≪≫
  Functor.isoWhiskerRight
    (eqToIso (BalancedTensor.rightTensorHomotopyFunctor_fac A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt d))) DerivedCategory.Qh ≪≫
  Functor.associator
    (BalancedTensor.rightTensorFunctor A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt d))
    (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)) DerivedCategory.Qh ≪≫
  Functor.isoWhiskerLeft
    (BalancedTensor.rightTensorFunctor A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt d))
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))

/-- 全てのK(End(E))射に自然な、再構成tensor評価とU12dの比較。 -/
def endomorphismTensorHomotopyEvaluationIso (d : D) :
    (endomorphismModuleTensor A D E).onHomotopy ⋙
        moduleHomotopyToDerivedClosed A D ⋙ moduleDerivedEvaluation A D d ≅
      BalancedTensor.rightTensorHomotopyFunctor A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) ⋙ DerivedCategory.Qh :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A (EndomorphismObject E)))
    (endomorphismTensorHomotopyEvaluationFacIso A D E d ≪≫
      (endomorphismU12dHomotopyTensorFacIso A D E d).symm)

/-- 任意の右射影解像度族について、導来tensorのD評価はU12dの導来tensorと自然同型。 -/
def endomorphismResolutionDerivedTensorEvaluationIso
    (R : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N) (d : D) :
    endomorphismResolutionDerivedTensor A D E R ⋙ moduleDerivedEvaluation A D d ≅
      moduleResolutionDerivedTensor A (EndomorphismObject E) R
        ((endomorphismModuleAction A D E).leftAt d) :=
  Functor.associator (moduleDerivedResolutionFunctor A (EndomorphismObject E) R)
    ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D)
    (moduleDerivedEvaluation A D d) ≪≫
  Functor.isoWhiskerLeft (moduleDerivedResolutionFunctor A (EndomorphismObject E) R)
    (Functor.associator (endomorphismModuleTensor A D E).onHomotopy
      (moduleHomotopyToDerivedClosed A D) (moduleDerivedEvaluation A D d) ≪≫
        endomorphismTensorHomotopyEvaluationIso A D E d)

/-- 主再構成導来tensorと既存U12d導来tensorの自然な評価正方形。 -/
def endomorphismDerivedTensorEvaluationIso (d : D) :
    endomorphismDerivedTensor A D E ⋙ moduleDerivedEvaluation A D d ≅
      moduleDerivedTensorRight A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) :=
  endomorphismResolutionDerivedTensorEvaluationIso A D E
    (moduleCanonicalProjectiveResolution A (EndomorphismObject E)) d

end SerrePositivity.DifferentialGraded
