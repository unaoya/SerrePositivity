module
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-! # 導来三角構造と比較の受入検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : IsTriangulated (DerivedModuleCategory A D) := inferInstance
example : (moduleHomotopyToDerivedClosed A D).IsTriangulated := inferInstance
example : (moduleHomotopyToDerivedClosed A D).IsLocalization
    (moduleHomotopyAcyclic A D).trW := inferInstance
#print axioms moduleHomotopyQuasiIsoLeftFractions
#print axioms moduleHomotopyQuasiIsoRightFractions
#print axioms moduleHomotopyQuasiIsoTriangulation
#print axioms moduleDerivedPreadditive
#print axioms moduleHomotopyToDerivedClosedAdditive
#print axioms moduleDerivedHasZeroObject
#print axioms moduleDerivedShiftAdditive
#print axioms moduleDerivedPretriangulated
#print axioms moduleHomotopyToDerivedClosedIsTriangulated
#print axioms moduleDerivedIsTriangulated
#print axioms moduleHomotopyToDerivedClosedArrowEssSurj
#print axioms moduleHomotopyToDerivedVerdierIsLocalization
#print axioms moduleDerived_distinguished_iff
#print axioms moduleHomotopyToDerivedIsTriangulated
#print axioms moduleHomotopyToDerivedArrowEssSurj
#print axioms moduleDerivedHomotopyInverseIsTriangulated
