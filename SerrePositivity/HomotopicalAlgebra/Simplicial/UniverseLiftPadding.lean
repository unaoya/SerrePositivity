module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLift

/-! # Natural removal of redundant padding in a simplicial universe lift -/

@[expose] public section
universe v a
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.UniverseLift

/-- The two lifts have the same value universe, with their actual wrappers identified explicitly. -/
def paddingIso : SSet.uliftFunctor.{a, v} ≅ SSet.uliftFunctor.{max a v, v} :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun x => ULift.up x.down
      invFun := fun x => ULift.up x.down
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }) (by intro n m θ; ext x; rfl))
    (by intro K L f; ext n x; rfl)

end SerrePositivity.SimplicialModel.UniverseLift
