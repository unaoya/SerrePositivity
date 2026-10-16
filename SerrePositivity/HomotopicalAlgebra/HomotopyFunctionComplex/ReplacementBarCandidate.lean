module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingDescent
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAugmentation

/-! # A strict auxiliary bar candidate on both undecorated base variables

Its unit and composition laws hold before localization. Its value universe
is max(u,v), not yet the required v. No model structure on that larger
simplicial-set category, Kan property, or comparison weak equivalence is assumed.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- The strict auxiliary object; it is not the final small RMap. -/
abbrev auxiliaryBar : (Cᵒᵖ × C) ⥤ SSet.{max u v} :=
  SimplicialModel.BarConstruction.relative (projection (C := C)) (uncurried hcof hfib)

lemma auxiliaryBar_degree (X : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ) :
    ((auxiliaryBar hcof hfib).obj X).obj n =
    ComposableArrows (CostructuredArrow
      (SimplicialModel.BarConstruction.elementProjection (projection (C := C))
        (uncurried hcof hfib) n) X) n.unop.len := rfl

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
