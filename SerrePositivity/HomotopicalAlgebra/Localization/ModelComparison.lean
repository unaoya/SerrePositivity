module

public import SerrePositivity.HomotopicalAlgebra.Localization.Conditional
public import SerrePositivity.HomotopicalAlgebra.Localization.ChoiceIndependence

/-! # Comparison of actual localization models

Inclusion of the localizing maps gives the identity Quillen adjunction.
Equal local-object predicates give equal model classes, independently of
the small generating presentation. Changing the original mapping-space
factorizations preserves the actual localization certificate.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [original : ModelCategory C]
  [simplicial : ModelCategory SSet.{v}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S T : MorphismProperty C} {m n : ModelCategory C}

namespace IsLocalizationModel
variable (hm : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hn : @IsLocalizationModel C _ original simplicial cof fib T n)

include hm hn in
lemma identity_isLeftQuillen_to (h : S ≤ T) :
    @Quillen.IsLeftQuillen C _ C _ m.categoryWithCofibrations
      m.categoryWithWeakEquivalences n.categoryWithCofibrations
      n.categoryWithWeakEquivalences (𝟭 C) := by
  let := original
  refine @Quillen.IsLeftQuillen.mk C _ C _ m.categoryWithCofibrations
    m.categoryWithWeakEquivalences n.categoryWithCofibrations
    n.categoryWithWeakEquivalences (𝟭 C) ?_ ?_
  · intro X Y f hf
    exact hn.cofibrations_eq.symm.le f (hm.cofibrations_eq.le f hf)
  · intro X Y f hf
    exact ⟨hn.cofibrations_eq.symm.le f (hm.cofibrations_eq.le f hf.1),
      hn.weakEquivalences_eq.symm.le f
        (MappingTests.localEquivalences_monotone _ _ h f (hm.weakEquivalences_eq.le f hf.2))⟩

include hm hn in
lemma classes_eq_of_localObjects_eq
    (h : @localObjects C _ original simplicial cof fib S =
      @localObjects C _ original simplicial cof fib T) :
    m.categoryWithCofibrations.cofibrations = n.categoryWithCofibrations.cofibrations ∧
      m.categoryWithWeakEquivalences.weakEquivalences =
        n.categoryWithWeakEquivalences.weakEquivalences ∧
      m.categoryWithFibrations.fibrations = n.categoryWithFibrations.fibrations := by
  let := original
  have hW : localEquivalences cof fib S = localEquivalences cof fib T :=
    MappingTests.localEquivalences_eq_of_localObjects _ _ h
  refine ⟨hm.cofibrations_eq.trans hn.cofibrations_eq.symm,
    hm.weakEquivalences_eq.trans (hW.trans hn.weakEquivalences_eq.symm), ?_⟩
  exact hm.fibrations_eq.trans
    ((congrArg (fun W => (original.categoryWithCofibrations.cofibrations ⊓ W).rlp) hW).trans
      hn.fibrations_eq.symm)

include hm in
lemma changeChoices
    (cof' : MorphismProperty.FunctorialFactorizationData
      (original.categoryWithCofibrations.cofibrations)
      (original.categoryWithFibrations.fibrations ⊓
        original.categoryWithWeakEquivalences.weakEquivalences))
    (fib' : MorphismProperty.FunctorialFactorizationData
      (original.categoryWithCofibrations.cofibrations ⊓
        original.categoryWithWeakEquivalences.weakEquivalences)
      original.categoryWithFibrations.fibrations)
    (hcof : simplicial.categoryWithCofibrations.cofibrations =
      MorphismProperty.monomorphisms _) :
    @IsLocalizationModel C _ original simplicial cof' fib' S m := by
  let := original
  refine @IsLocalizationModel.mk C _ original simplicial cof' fib' S m
    hm.cofibrations_eq ?_ (fun Y => ?_)
  · exact hm.weakEquivalences_eq.trans
      (localEquivalences_choices_eq cof cof' fib fib' hcof S)
  · exact (hm.fibrant_iff Y).trans
      (congrArg (fun P : C → Prop => P Y)
        (localFibrantObjects_choices_eq cof cof' fib fib' hcof S)).to_iff

end IsLocalizationModel
end SerrePositivity.Bousfield
