module
public import SerrePositivity.DifferentialGraded.Bimodule.OfActions

/-! # 全次数自然な作用族とbimoduleの往復検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
example (M : Bimodule A B C) :
    Bimodule.ofParamTrans A B C M.rightAt M.paramTrans M.paramTrans_unit M.paramTrans_comp = M :=
  M.ofParamTrans_recover
#print axioms Bimodule.ofParamTrans
#print axioms Bimodule.ofParamTrans_map_π
#print axioms Bimodule.paramTrans
#print axioms Bimodule.paramTrans_unit
#print axioms Bimodule.paramTrans_comp
#print axioms Bimodule.ofParamTrans_recover
