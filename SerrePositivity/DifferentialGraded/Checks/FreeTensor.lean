module
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import Mathlib.Data.ZMod.Basic

/-! # U6a の自由加群対象・作用・underlying family の検証 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
example (K : Complex A) : DGFunctor A (Complex A) (Complex A) := tensorLeftDG K
example (x y : D) (K : Complex A) :
    (freeModule x K).obj (op y) = K ⊗ (y ⟶[Complex A] x) := rfl
example [Small.{u} D] : (moduleUnderlying A D).Faithful := inferInstance
example (P K : Complex (ZMod 2)) : RightModule (ZMod 2) (Complex (ZMod 2)) :=
  freeModule P K
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.tensorLeftHom_apply
#print axioms SerrePositivity.DifferentialGraded.tensorLeftHom_id
#print axioms SerrePositivity.DifferentialGraded.tensorLeftHom_comp
#print axioms SerrePositivity.DifferentialGraded.tensorLeftDG
#print axioms SerrePositivity.DifferentialGraded.tensorModule_action
#print axioms SerrePositivity.DifferentialGraded.moduleUnderlying_faithful
