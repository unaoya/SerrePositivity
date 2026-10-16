module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLift

/-! # A natural flattening isomorphism for two actual simplicial universe lifts -/

@[expose] public section
universe v a b
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.UniverseLift

/-- Flatten wrappers without identifying the independent universe parameters. -/
def iterationIso : SSet.uliftFunctor.{a, v} ⋙ SSet.uliftFunctor.{b, max a v} ≅
    SSet.uliftFunctor.{max a b, v} :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun x => ULift.up x.down.down
      invFun := fun x => ULift.up (ULift.up x.down)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }) (by intro n m θ; ext x; rfl))
    (by intro K L f; ext n x; rfl)

end SerrePositivity.SimplicialModel.UniverseLift
