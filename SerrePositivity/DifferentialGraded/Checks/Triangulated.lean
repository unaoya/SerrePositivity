module
public import SerrePositivity.DifferentialGraded.Module.Triangulated

/-! # K(D)の八面体公理の受入検査 -/
@[expose] public section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : IsTriangulated (ModuleHomotopyCategory A D) := inferInstance
#print axioms moduleHomotopyIsTriangulated
