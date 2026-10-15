module

public import SerrePositivity.HomotopicalAlgebra.Localization.Detection
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction

/-! # Conditional API for a left Bousfield localization model

A certificate receives an actual Mathlib model structure on the same C.
It records the original cofibrations, the proved mapping-test definition
of weak equivalences, and the intended fibrant objects. This file proves
consequences of a certificate and does not assume or assert its existence.
The original and candidate model classes are kept explicit throughout.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [original : ModelCategory C]
  [simplicial : ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

structure IsLocalizationModel (S : MorphismProperty C) (m : ModelCategory C) : Prop where
  cofibrations_eq : m.categoryWithCofibrations.cofibrations =
    original.categoryWithCofibrations.cofibrations
  weakEquivalences_eq : m.categoryWithWeakEquivalences.weakEquivalences =
    @localEquivalences C _ original simplicial cof fib S
  fibrant_iff (Y : C) : m.categoryWithFibrations.fibrations (terminal.from Y) ↔
    @localFibrantObjects C _ original simplicial cof fib S Y

namespace IsLocalizationModel
variable {cof fib} {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)

include h

lemma fibrations_eq : m.categoryWithFibrations.fibrations =
    (original.categoryWithCofibrations.cofibrations ⊓
      @localEquivalences C _ original simplicial cof fib S).rlp := by
  let := original
  have hm : m.categoryWithFibrations.fibrations =
      (m.categoryWithCofibrations.cofibrations ⊓
        m.categoryWithWeakEquivalences.weakEquivalences).rlp := by
    let := m
    exact (trivialCofibrations_rlp C).symm
  rw [h.cofibrations_eq, h.weakEquivalences_eq] at hm
  exact hm

lemma trivialFibrations_eq :
    m.categoryWithFibrations.fibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences =
      original.categoryWithFibrations.fibrations ⊓
        original.categoryWithWeakEquivalences.weakEquivalences := by
  let := original
  have hm : m.categoryWithFibrations.fibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences =
      m.categoryWithCofibrations.cofibrations.rlp := by
    let := m
    exact (cofibrations_rlp C).symm
  have ho : original.categoryWithCofibrations.cofibrations.rlp =
      original.categoryWithFibrations.fibrations ⊓
        original.categoryWithWeakEquivalences.weakEquivalences := cofibrations_rlp C
  exact hm.trans ((congrArg MorphismProperty.rlp h.cofibrations_eq).trans ho)

lemma identity_isLeftQuillen
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _) :
    @Quillen.IsLeftQuillen C _ C _ original.categoryWithCofibrations
      original.categoryWithWeakEquivalences
      m.categoryWithCofibrations m.categoryWithWeakEquivalences (𝟭 C) := by
  let := original
  refine @Quillen.IsLeftQuillen.mk C _ C _ original.categoryWithCofibrations
    original.categoryWithWeakEquivalences m.categoryWithCofibrations
    m.categoryWithWeakEquivalences (𝟭 C) ?_ ?_
  · intro X Y f hf
    change m.categoryWithCofibrations.cofibrations f
    rw [h.cofibrations_eq]
    exact hf
  · intro X Y f hf
    change m.categoryWithCofibrations.cofibrations f ∧
      m.categoryWithWeakEquivalences.weakEquivalences f
    rw [h.cofibrations_eq, h.weakEquivalences_eq]
    exact ⟨hf.1, weakEquivalences_le_localEquivalences cof fib hcof S f hf.2⟩

lemma fibrations_le_original
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _) :
    m.categoryWithFibrations.fibrations ≤ original.categoryWithFibrations.fibrations := by
  let := original
  have ho : (original.categoryWithCofibrations.cofibrations ⊓
      original.categoryWithWeakEquivalences.weakEquivalences).rlp =
      original.categoryWithFibrations.fibrations := trivialCofibrations_rlp C
  refine h.fibrations_eq.le.trans ((MorphismProperty.antitone_rlp ?_).trans ho.le)
  intro X Y f hf
  exact ⟨hf.1, weakEquivalences_le_localEquivalences cof fib hcof S f hf.2⟩

lemma classes_recover_of_le
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (hS : S ≤ original.categoryWithWeakEquivalences.weakEquivalences) :
    m.categoryWithCofibrations.cofibrations = original.categoryWithCofibrations.cofibrations ∧
      m.categoryWithWeakEquivalences.weakEquivalences =
        original.categoryWithWeakEquivalences.weakEquivalences ∧
      m.categoryWithFibrations.fibrations = original.categoryWithFibrations.fibrations := by
  let := original
  have hw := localEquivalences_eq_weakEquivalences_of_le cof fib hcof hfib hS
  refine ⟨h.cofibrations_eq, h.weakEquivalences_eq.trans hw, ?_⟩
  rw [h.fibrations_eq, hw]
  exact trivialCofibrations_rlp C

end IsLocalizationModel

/-- Original weak equivalences require no change of model structure. -/
lemma original_isLocalizationModel_of_le
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    {S : MorphismProperty C} (hS : S ≤ weakEquivalences C) :
    IsLocalizationModel cof fib S original where
  cofibrations_eq := rfl
  weakEquivalences_eq :=
    (localEquivalences_eq_weakEquivalences_of_le cof fib hcof hfib hS).symm
  fibrant_iff Y := (fibration_iff (terminal.from Y)).symm.trans
    (localFibrantObjects_iff_of_le cof fib hcof hS Y).symm

end SerrePositivity.Bousfield
