module
public import SerrePositivity.DifferentialGraded.Module.ConeShift

/-! # 加群圏のcone shift同型の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleShiftObj A D s (moduleCone A D f) ≅ moduleCone A D (moduleShiftMap A D s f) :=
  moduleConeShiftIso A D s f

#print axioms moduleConeShiftFirst
#print axioms moduleConeShiftSecond
#print axioms moduleConeShiftLeftInput
#print axioms moduleConeShiftFirst_π
#print axioms moduleConeShiftSecond_π
#print axioms moduleConeShiftLeftInput_π
#print axioms moduleConeShiftFirst_closed
#print axioms moduleConeShiftInputs_cycle
#print axioms moduleConeShiftLeftInput_d
#print axioms moduleConeShiftHom
#print axioms moduleConeShiftInv
#print axioms moduleConeShiftHom_eval
#print axioms moduleConeShiftInv_eval
#print axioms moduleConeShift_hom_inv
#print axioms moduleConeShift_inv_hom
#print axioms moduleConeShiftIso
