module
public import SerrePositivity.DifferentialGraded.Module.Pretriangulated

/-! # K(D)のpretriangulated構造の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Pretriangulated SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : Pretriangulated (ModuleHomotopyCategory A D) := inferInstance

example (T : Triangle (ModuleHomotopyCategory A D)) :
    T ∈ distTriang (ModuleHomotopyCategory A D) ↔ T ∈ moduleDistinguishedTriangles A D :=
  moduleHomotopy_distinguished_iff A D T

example (T : Triangle (ModuleHomotopyCategory A D)) :
    T ∈ moduleDistinguishedTriangles A D ↔ T.rotate ∈ moduleDistinguishedTriangles A D :=
  moduleDistinguished_rotate_iff A D T

#print axioms triangleShiftIsoTrans
#print axioms moduleHomotopyConeShiftIso
#print axioms moduleDistinguished_ofConeIso
#print axioms moduleDistinguished_shift
#print axioms moduleDistinguished_invRotate
#print axioms moduleDistinguished_rotate_iff
#print axioms moduleHomotopyPretriangulated
#print axioms moduleHomotopy_distinguished_iff
