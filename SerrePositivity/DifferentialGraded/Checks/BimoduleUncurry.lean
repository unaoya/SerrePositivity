module
public import SerrePositivity.DifferentialGraded.Bimodule.Uncurry

/-! # 実際のuncurried dg関手と両作用の回復 -/
@[expose] public section
noncomputable section
universe u v w
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
example (M : Bimodule A B C) : BimoduleTensorFunctor A B C := M.toTensorFunctor
#print axioms Bimodule.toTensorFunctor
#print axioms Bimodule.toTensorFunctor_rightAt
#print axioms Bimodule.toTensorFunctor_leftAt
