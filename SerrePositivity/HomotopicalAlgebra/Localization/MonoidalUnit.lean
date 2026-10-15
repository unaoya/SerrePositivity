module

public import SerrePositivity.HomotopicalAlgebra.Localization.Conditional
public import SerrePositivity.HomotopicalAlgebra.Monoidal.UnitChangeModel

/-! # The unit axiom for an actual ordinary localization

The original unit replacement still satisfies the separate unit axiom.
This neither assumes a cofibrant unit nor asserts tensor compatibility.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {C : Type u} [Category.{v} C] [original : ModelCategory C] [MonoidalCategory C]
  [simplicial : ModelCategory SSet.{v}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)

include h hcof in
lemma hasUnitAxiom (hu : @Quillen.HasUnitAxiom C _ original _) : @Quillen.HasUnitAxiom C _ m _ := by
  let := original
  exact Quillen.hasUnitAxiom_change_model original m h.cofibrations_eq
    ((weakEquivalences_le_localEquivalences cof fib hcof S).trans h.weakEquivalences_eq.symm.le) hu

end SerrePositivity.Bousfield.IsLocalizationModel
