module
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated

/-! # 全dg自然な回転比較と三角形の回転同型の受入検査 -/
@[expose] public section
universe u v
open CategoryTheory Pretriangulated SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ moduleDistinguishedTriangles A D) : T.rotate ∈ moduleDistinguishedTriangles A D :=
  moduleDistinguished_rotate A D T hT

#print axioms moduleConeRotationConnectingElement
#print axioms moduleConeRotationContractingElement
#print axioms moduleConeRotationConnectingElement_π
#print axioms moduleConeRotationContractingElement_π
#print axioms moduleConeRotationContractingElement_d
#print axioms moduleConeRotationInvHomHomotopy
#print axioms moduleConeRotationConnectingElement_d
#print axioms moduleConeRotationConnectingHomotopy
#print axioms moduleConeRotation_connecting
#print axioms moduleConeRotationHomotopyIso
#print axioms moduleConeRotationShiftIso
#print axioms moduleConeRotation_connecting_homotopy
#print axioms moduleHomotopyConeRotationIso
#print axioms moduleDistinguished_rotate
#print axioms moduleDistinguished_comp_zero₂₃
#print axioms moduleDistinguished_comp_zero₃₁
