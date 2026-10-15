module
public import SerrePositivity.DifferentialGraded.Derived.HomotopyShift

/-! # K(D)から主導来圏への局所化のshift整合性の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : (moduleHomotopyToDerivedClosed A D).CommShift ℤ := inferInstance
#print axioms moduleHomotopyDerivedInverseLifting
#print axioms moduleHomotopyDerivedInverseCommShift
#print axioms moduleHomotopyDerivedInverseComparisonCommShift
#print axioms moduleHomotopyToDerivedClosedCommShift
#print axioms moduleToHomotopyDerivedIsoCommShift
