module
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopy

/-! # 全Hom dg shiftと既存K(D)の整数shiftとの自然比較 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実際のdg shiftのH⁰関手は、既存の商圏shiftと自然同型で一致する。 -/
def moduleShiftDGHomotopyIso (s : ℤ) :
    (moduleShiftDG A D s).onHomotopy ≅ shiftFunctor (ModuleHomotopyCategory A D) s :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    (eqToIso ((moduleShiftDG A D s).onHomotopy_fac) ≪≫
      Functor.isoWhiskerRight (eqToIso (moduleShiftDG_onClosed_eq A D s)) (moduleToHomotopy A D) ≪≫
      (moduleToHomotopy A D).commShiftIso s)

end SerrePositivity.DifferentialGraded
