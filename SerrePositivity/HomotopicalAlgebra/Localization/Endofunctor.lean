module

public import SerrePositivity.HomotopicalAlgebra.Localization.UniversalProperty

/-! # Extending an original Quillen endofunctor to the localized model

The exact extra condition is that its derived image of each localizing
map is a local equivalence. Both the source and target of the functor
carry the localized model in the conclusion.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {C : Type u} [Category.{v} C] [original : ModelCategory C]
  [simplicial : ModelCategory SSet.{v}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfib : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{v}.rlp)
  {F R : C ⥤ C} (adj : F ⊣ R)
  (hF : @Quillen.IsLeftQuillen C _ C _ original.categoryWithCofibrations
    original.categoryWithWeakEquivalences original.categoryWithCofibrations
    original.categoryWithWeakEquivalences F)

include h hcof hfib adj hF in
lemma endofunctor_isLeftQuillen_iff :
    @Quillen.IsLeftQuillen C _ C _ m.categoryWithCofibrations m.categoryWithWeakEquivalences
      m.categoryWithCofibrations m.categoryWithWeakEquivalences F ↔
    ∀ {X Y : C} (f : X ⟶ Y), S f → (@localEquivalences C _ original simplicial cof fib S)
      (F.map ((@cofibrantSource C _ original cof).map f)) := by
  let := original
  have hw := weakEquivalences_le_localEquivalences cof fib hcof S
  have hFn : @Quillen.IsLeftQuillen C _ C _ original.categoryWithCofibrations
      original.categoryWithWeakEquivalences m.categoryWithCofibrations
      m.categoryWithWeakEquivalences F := by
    refine @Quillen.IsLeftQuillen.mk C _ C _ original.categoryWithCofibrations
      original.categoryWithWeakEquivalences m.categoryWithCofibrations
      m.categoryWithWeakEquivalences F ?_ ?_
    · exact fun _ _ f hf => h.cofibrations_eq.symm.le _ (hF.map_cofibrations f hf)
    · intro X Y f hf
      have ht := hF.map_trivialCofibrations f hf
      exact ⟨h.cofibrations_eq.symm.le _ ht.1, h.weakEquivalences_eq.symm.le _ (hw _ ht.2)⟩
  refine (h.leftQuillen_iff_cofibrant_test (target := m) hcof hfib adj hFn
    hcof hfib hcof hfib).trans ?_
  constructor
  · exact fun hS _ _ f hf => h.weakEquivalences_eq.le _ (hS f hf)
  · exact fun hS _ _ f hf => h.weakEquivalences_eq.symm.le _ (hS f hf)

include h hcof hfib adj hF in
/-- Preservation of local objects by the actual right adjoint extends the
original endofunctor to the localized model in both variables. -/
lemma endofunctor_isLeftQuillen_of_rightAdjoint_local
    (hR : ∀ Y : C, m.categoryWithFibrations.fibrations (Limits.terminal.from Y) →
      @localObjects C _ original simplicial cof fib S (R.obj Y)) :
    @Quillen.IsLeftQuillen C _ C _ m.categoryWithCofibrations m.categoryWithWeakEquivalences
      m.categoryWithCofibrations m.categoryWithWeakEquivalences F := by
  let := original
  have hw := weakEquivalences_le_localEquivalences cof fib hcof S
  have hFn : @Quillen.IsLeftQuillen C _ C _ original.categoryWithCofibrations
      original.categoryWithWeakEquivalences m.categoryWithCofibrations
      m.categoryWithWeakEquivalences F := by
    refine @Quillen.IsLeftQuillen.mk C _ C _ original.categoryWithCofibrations
      original.categoryWithWeakEquivalences m.categoryWithCofibrations
      m.categoryWithWeakEquivalences F ?_ ?_
    · exact fun _ _ f hf => h.cofibrations_eq.symm.le _ (hF.map_cofibrations f hf)
    · intro X Y f hf
      have ht := hF.map_trivialCofibrations f hf
      exact ⟨h.cofibrations_eq.symm.le _ ht.1, h.weakEquivalences_eq.symm.le _ (hw _ ht.2)⟩
  apply (h.leftQuillen_iff_rightAdjoint_local (target := m) hcof hfib adj hFn).mpr
  intro Y hY
  exact hR Y ((@fibration_iff C _ _ _ (Limits.terminal.from Y) m.categoryWithFibrations).mp hY)

end SerrePositivity.Bousfield.IsLocalizationModel
