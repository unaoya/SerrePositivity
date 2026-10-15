module
public import SerrePositivity.DifferentialGraded.Derived.Evaluation
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopy

/-! # 指定局所化の整数 shift と導来評価の CommShift -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

instance moduleEvaluationToDerivedCommShift (x : D) :
    (moduleEvaluationToDerived A D x).CommShift ℤ := by
  unfold moduleEvaluationToDerived
  infer_instance

/-- 厳密な因子化をMathlibの局所化Liftingとして登録する。 -/
instance moduleDerivedEvaluationLifting (x : D) :
    Localization.Lifting (moduleToDerived A D) (moduleQuasiIso A D)
      (moduleEvaluationToDerived A D x) (moduleDerivedEvaluation A D x) :=
  ⟨eqToIso (moduleDerivedEvaluation_fac A D x)⟩

/-- 導来評価は整数shiftと、そのzero/add coherenceを保存する。 -/
instance moduleDerivedEvaluationCommShift (x : D) :
    (moduleDerivedEvaluation A D x).CommShift ℤ :=
  Functor.commShiftOfLocalization (moduleToDerived A D) (moduleQuasiIso A D) ℤ
    (moduleEvaluationToDerived A D x) (moduleDerivedEvaluation A D x)

/-- 導来評価の因子化自然同型もshiftに整合する。 -/
instance moduleDerivedEvaluationFacCommShift (x : D) :
    NatTrans.CommShift (eqToIso (moduleDerivedEvaluation_fac A D x)).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleToDerived A D) (moduleQuasiIso A D)
      (moduleEvaluationToDerived A D x) (moduleDerivedEvaluation A D x)).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization (moduleToDerived A D) (moduleQuasiIso A D) ℤ
    (moduleEvaluationToDerived A D x) (moduleDerivedEvaluation A D x)

end SerrePositivity.DifferentialGraded
