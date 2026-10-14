/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import SerrePositivity.CategoryTheory.MorphismProperty.UnderFactorization
public import SerrePositivity.CategoryTheory.LiftingProperties.Under
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# The model category structure on Under categories

Dual adaptation of Mathlib's `AlgebraicTopology/ModelCategory/Over.lean`
at e6bbacd0e1b7307ff6e17da09cd2455f60804fa6.
The three classes are inverse images along `Under.forget S`; both
factorizations and lifting properties use the underlying arrows explicitly.
No hypothesis on the object S is required.
-/

@[expose] public section

universe v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] (S : C)

/-- Expose the existing structured-arrow finite limits on the `Under` type.
The explicit specialization avoids relying on typeclass unfolding of `Under`. -/
instance CategoryTheory.Under.hasFiniteLimits [CategoryTheory.Limits.HasFiniteLimits C] :
    CategoryTheory.Limits.HasFiniteLimits (Under S) :=
  inferInstanceAs (CategoryTheory.Limits.HasFiniteLimits (StructuredArrow S (𝟭 C)))

namespace HomotopicalAlgebra

section

variable [CategoryWithCofibrations C]

instance : CategoryWithCofibrations (Under S) where
  cofibrations := (cofibrations C).under

lemma cofibrations_under_def :
    cofibrations (Under S) = (cofibrations C).under := rfl

lemma cofibrations_under_iff {X Y : Under S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.right := by
  simp only [cofibration_iff, cofibrations_under_def, MorphismProperty.under_iff]

instance {X Y : Under S} (f : X ⟶ Y) [Cofibration f] : Cofibration f.right := by
  rwa [← cofibrations_under_iff]

instance [(cofibrations C).IsStableUnderRetracts] :
    (cofibrations (Under S)).IsStableUnderRetracts := by
  rw [cofibrations_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithFibrations C]

instance : CategoryWithFibrations (Under S) where
  fibrations := (fibrations C).under

lemma fibrations_under_def :
    fibrations (Under S) = (fibrations C).under := rfl

lemma fibrations_under_iff {X Y : Under S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.right := by
  simp only [fibration_iff, fibrations_under_def, MorphismProperty.under_iff]

instance {X Y : Under S} (f : X ⟶ Y) [Fibration f] : Fibration f.right := by
  rwa [← fibrations_under_iff]

instance [(fibrations C).IsStableUnderRetracts] :
    (fibrations (Under S)).IsStableUnderRetracts := by
  rw [fibrations_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithWeakEquivalences C]

instance : CategoryWithWeakEquivalences (Under S) where
  weakEquivalences := (weakEquivalences C).under

lemma weakEquivalences_under_def :
    weakEquivalences (Under S) = (weakEquivalences C).under := rfl

lemma weakEquivalences_under_iff {X Y : Under S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.right := by
  simp only [weakEquivalence_iff, weakEquivalences_under_def, MorphismProperty.under_iff]

instance {X Y : Under S} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.right := by
  rwa [← weakEquivalences_under_iff]

instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences (Under S)).IsStableUnderRetracts := by
  rw [weakEquivalences_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end

lemma trivialCofibrations_under_eq
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] :
    trivialCofibrations (Under S) = (trivialCofibrations C).under := rfl

lemma trivialFibrations_under_eq
    [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] :
    trivialFibrations (Under S) = (trivialFibrations C).under := rfl

instance [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences (Under S)).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

section

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
  [CategoryWithFibrations C]

instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (trivialCofibrations (Under S)).HasFactorization (fibrations (Under S)) := by
  rw [fibrations_under_def, trivialCofibrations_under_eq]
  infer_instance

instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (cofibrations (Under S)).HasFactorization (trivialFibrations (Under S)) := by
  rw [cofibrations_under_def, trivialFibrations_under_eq]
  infer_instance

end

instance ModelCategory.under [ModelCategory C] : ModelCategory (Under S) where
  cm4a _ _ _ _ _ := .under _ _
  cm4b _ _ _ _ _ := .under _ _

end HomotopicalAlgebra
