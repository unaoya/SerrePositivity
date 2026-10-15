module
public import SerrePositivity.DifferentialGraded.Bimodule.TensorComparison
public import Mathlib.Data.ZMod.Basic

/-! # U11b：bimoduleのcurried/uncurried表示の両往復 -/
@[expose] public section
noncomputable section
universe u v w
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
example : Bimodule A B C ≃ BimoduleTensorFunctor A B C := bimoduleEquivTensorFunctor A B C
example (M : Bimodule A B C) : M.toTensorFunctor.toBimodule = M := M.toTensorFunctor_toBimodule
example (F : BimoduleTensorFunctor A B C) : F.toBimodule.toTensorFunctor = F :=
  F.toBimodule_toTensorFunctor
example (M : Bimodule ℤ PUnit.{1} PUnit.{1}) : M.toTensorFunctor.toBimodule = M :=
  M.toTensorFunctor_toBimodule
example (F : BimoduleTensorFunctor (ZMod 2) PUnit.{1} PUnit.{1}) :
    F.toBimodule.toTensorFunctor = F := F.toBimodule_toTensorFunctor
#print axioms Bimodule.ext_rightAt_leftAt
#print axioms BimoduleTensorFunctor.toBimodule_rightAt
#print axioms BimoduleTensorFunctor.toBimodule_leftAt
#print axioms BimoduleTensorFunctor.map_tensorElement
#print axioms Bimodule.toTensorFunctor_toBimodule
#print axioms BimoduleTensorFunctor.toBimodule_toTensorFunctor
#print axioms bimoduleEquivTensorFunctor
