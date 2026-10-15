module
public import SerrePositivity.DifferentialGraded.Derived.HomotopyComparison
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopy
public import Mathlib.CategoryTheory.Shift.Localization

/-! # K(D)から主導来圏への局所化関手の整合的shift -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleHomotopyDerivedInverseLifting :
    Localization.Lifting (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D)
      (moduleQuasiIso A D) (moduleToDerived A D) (moduleDerivedHomotopyEquivalence A D).inverse :=
  ⟨moduleDerivedHomotopyInverseComparisonIso A D⟩

instance moduleHomotopyDerivedInverseCommShift :
    (moduleDerivedHomotopyEquivalence A D).inverse.CommShift ℤ :=
  Functor.commShiftOfLocalization (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D)
    (moduleQuasiIso A D) ℤ (moduleToDerived A D) (moduleDerivedHomotopyEquivalence A D).inverse

instance moduleHomotopyDerivedInverseComparisonCommShift :
    NatTrans.CommShift (moduleDerivedHomotopyInverseComparisonIso A D).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D)
      (moduleQuasiIso A D) (moduleToDerived A D)
      (moduleDerivedHomotopyEquivalence A D).inverse).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) (moduleQuasiIso A D) ℤ
    (moduleToDerived A D) (moduleDerivedHomotopyEquivalence A D).inverse

instance moduleHomotopyToDerivedClosedCommShift :
    (moduleHomotopyToDerivedClosed A D).CommShift ℤ := by
  unfold moduleHomotopyToDerivedClosed
  infer_instance

instance moduleToHomotopyDerivedIsoCommShift :
    NatTrans.CommShift (moduleToHomotopyDerivedIso A D).hom ℤ := by
  change NatTrans.CommShift
    ((Functor.associator (moduleToHomotopy A D) (moduleHomotopyToDerived A D)
      (moduleDerivedHomotopyEquivalence A D).inverse).inv ≫
        (moduleDerivedHomotopyInverseComparisonIso A D).hom) ℤ
  apply NatTrans.CommShift.comp

end SerrePositivity.DifferentialGraded
