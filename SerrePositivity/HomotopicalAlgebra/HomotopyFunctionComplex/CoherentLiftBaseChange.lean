module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftFunctorLaws

/-! # Actual base change of coherent lift tuples and their interpolation -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftBaseChange
variable {C : Type u} [Category.{v} C] [ModelCategory C]

def strict {X Y : ResolutionObject C} {f g : X.base ⟶ Y.base} (h : f = g)
    (k : CoherentLiftTuples.StrictLift X Y f) : CoherentLiftTuples.StrictLift X Y g :=
  ⟨k.val, k.property.trans h⟩

def tuples {X Y : ResolutionObject C} {f g : X.base ⟶ Y.base} (h : f = g) :
    CoherentLiftTuples.obj X Y f ⟶ CoherentLiftTuples.obj X Y g := VertexTuples.map (strict h)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

lemma interpolation {X Y : ResolutionObject C} {f g : X.base ⟶ Y.base} (h : f = g) :
    CoherentLiftTuples.interpolation hcof X Y f ≫ ResolutionLiftSpace.baseChange h =
      tuples h ≫ CoherentLiftTuples.interpolation hcof X Y g := by
  cases h
  change _ ≫ (𝟙 _) = (𝟙 _) ≫ _
  rw [Category.comp_id, Category.id_comp]

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftBaseChange
