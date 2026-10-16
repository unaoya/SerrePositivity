module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftTensor
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-! # Lift the same whole simplicial homotopy without a model structure -/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.UniverseLift
variable {K P : SSet.{v}} {f g : K ⟶ P}

/-- The actual lifted interval family, retaining both endpoint maps. -/
def homotopy (H : SSet.Homotopy f g) : SSet.Homotopy (map.{w} f) (map.{w} g) where
  h := simplexTensorMap.{w} H.h
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (congrArg (fun k => k.app n x.down) H.h₀)
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (congrArg (fun k => k.app n x.down) H.h₁)
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

end SerrePositivity.SimplicialModel.UniverseLift
