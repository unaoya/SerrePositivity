module
public import SerrePositivity.DifferentialGraded.Bimodule.Tensor

/-! # tensor積上のdg関手からbimoduleへの変換の受入 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
example (F : BimoduleTensorFunctor A B C) : Bimodule A B C := F.toBimodule
example (F : BimoduleTensorFunctor A B C) (c d : C) (b : B) :
    F.toBimodule.toFunctor.map c d ≫
      moduleHomπ A B (F.rightAt c) (F.rightAt d) b = (F.leftAt b).map c d :=
  F.toBimodule_map_π c d b
#print axioms BimoduleTensorFunctor
#print axioms BimoduleTensorFunctor.rightAt
#print axioms BimoduleTensorFunctor.leftAt
#print axioms BimoduleTensorFunctor.interchange
#print axioms BimoduleTensorFunctor.paramTrans
#print axioms BimoduleTensorFunctor.toBimodule
#print axioms BimoduleTensorFunctor.toBimodule_map_π
