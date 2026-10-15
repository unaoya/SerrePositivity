module

public import SerrePositivity.HomotopicalAlgebra.Localization.Basic

/-! # Independence of the actual mapping-space choices

The previously constructed natural weak-equivalence cospan compares the
mapping tests for two actual source resolutions and fibrant replacements.
Consequently the predicates and classes agree as equalities. This does not
assert an equality of the mapping bifunctors themselves.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof₁ cof₂ : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))
  (fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma mappingTest_choices_eq (Y : C) :
    mappingTest cof₁ fib₁ Y = mappingTest cof₂ fib₂ Y := by
  have h₁ := MappingTests.test_eq_of_weakComparison (chosenResolutionHom cof₁ fib₁)
    (weakEquivalences SSet.{v})
    (ChosenComparison.left cof₁ cof₁ cof₂ fib₁ fib₁ fib₂)
    (ChosenComparison.left_weakEquivalence cof₁ cof₁ cof₂ fib₁ fib₁ fib₂ hcof) Y
  have h₂ := MappingTests.test_eq_of_weakComparison (chosenResolutionHom cof₂ fib₂)
    (weakEquivalences SSet.{v})
    (ChosenComparison.right cof₁ cof₁ cof₂ fib₁ fib₁ fib₂)
    (ChosenComparison.right_weakEquivalence cof₁ cof₁ cof₂ fib₁ fib₁ fib₂ hcof) Y
  exact h₁.trans h₂.symm

include hcof in
lemma localObjects_choices_eq (S : MorphismProperty C) :
    localObjects cof₁ fib₁ S = localObjects cof₂ fib₂ S :=
  MappingTests.localObjects_eq_of_tests _ _
    (mappingTest_choices_eq cof₁ cof₂ fib₁ fib₂ hcof) S

include hcof in
lemma localEquivalences_choices_eq (S : MorphismProperty C) :
    localEquivalences cof₁ fib₁ S = localEquivalences cof₂ fib₂ S :=
  MappingTests.localEquivalences_eq_of_tests _ _
    (mappingTest_choices_eq cof₁ cof₂ fib₁ fib₂ hcof) S

include hcof in
lemma localFibrantObjects_choices_eq (S : MorphismProperty C) :
    localFibrantObjects cof₁ fib₁ S = localFibrantObjects cof₂ fib₂ S := by
  funext Y
  unfold localFibrantObjects
  rw [localObjects_choices_eq cof₁ cof₂ fib₁ fib₂ hcof S]

include hcof in
lemma localEquivalences_strictMap (S : MorphismProperty C) (Q : C ⥤ C)
    (q : Q ⟶ 𝟭 C) (hq : ∀ X, weakEquivalences C (q.app X)) :
    localEquivalences cof₁ fib₁ (S.strictMap Q) = localEquivalences cof₁ fib₁ S := by
  apply MappingTests.localEquivalences_eq_of_localObjects
  funext Y
  exact propext (localObjects_strictMap cof₁ fib₁ hcof S Q q hq Y)

end SerrePositivity.Bousfield
