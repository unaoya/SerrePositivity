module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource

/-! # The actual coherent choices on the ordinary simplex diagram with fixed objects -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedChoices
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedSource
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

abbrev target := OrdinaryBarParameterChoiceCategory.diagram (C := C) hcof hfib P

def transported : diagram C ⟶ target (C := C) hcof hfib P :=
  (comparisonIso C).hom ≫ OrdinaryBarFreeResolutionNaturalChoice.choices hcof hfib P

lemma transported_app (n : SimplexCategoryᵒᵖ) : (transported (C := C) hcof hfib P).app n =
    (OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n.unop.len).toCatHom := by
  rw [transported, NatTrans.comp_app, OrdinaryBarFreeResolutionNaturalChoice.choices_app]
  change comparison C n ≫ (eqToHom (degree_power (D C) (n.unop.len + 1)).symm ≫ _) = _
  simp [comparison]

def choices : literal C ⟶ target (C := C) hcof hfib P where
  app n := (OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n.unop.len).toCatHom
  naturality {n m} θ := by
    have h := (transported (C := C) hcof hfib P).naturality θ
    rw [transported_app, transported_app] at h
    change (literalMap C θ).toCatHom ≫ _ = _
    rw [show (literalMap C θ).toCatHom = (diagram C).map θ from Cat.Hom.ext (literalMap_eq C θ)]
    exact h

def action (n : SimplexCategoryᵒᵖ) : (literal C).obj n ⥤
    ParameterCategory.Object (OrdinaryBarFreeResolutionAction.parameters P n) :=
  OrdinaryBarFreeAmbientFamilies.fixedAction hcof hfib P n.unop.len

lemma action_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    literalMap C θ ⋙ action hcof hfib P m =
      action hcof hfib P n ⋙ ParameterCategory.reindex (P ◁ SSet.stdSimplex.map θ.unop) := by
  have h := congrArg Cat.Hom.toFunctor ((choices (C := C) hcof hfib P).naturality θ)
  change literalMap C θ ⋙ OrdinaryBarFreeResolutionChoices.diagram hcof hfib P m.unop.len =
    OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n.unop.len ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.map θ.unop) at h
  unfold action
  rw [OrdinaryBarFreeAmbientFamilies.fixedAction_eq, OrdinaryBarFreeAmbientFamilies.fixedAction_eq]
  unfold OrdinaryBarFreeAmbientFamilies.evaluated
  rw [← CategoryTheory.Functor.assoc, h, CategoryTheory.Functor.assoc,
    OrdinaryBarChoiceCategory.reindex_evaluation]
  rfl

lemma action_obj (n : SimplexCategoryᵒᵖ) (X : D C) : (action hcof hfib P n).obj X =
    OrdinaryBarFreeAmbientFamilies.ambientObject hcof hfib P n.unop.len X := rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedChoices
