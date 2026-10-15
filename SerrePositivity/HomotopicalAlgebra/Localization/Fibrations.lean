module

public import SerrePositivity.HomotopicalAlgebra.Localization.Conditional
public import SerrePositivity.HomotopicalAlgebra.Localization.LocalReplacementDetection
public import SerrePositivity.HomotopicalAlgebra.Localization.ReplacementData

/-! # Localized fibrations between local objects

An original fibration with local source and local fibrant target is a
localized fibration. Factor in the localized model, detect the resulting
trivial cofibration as an original weak equivalence between local objects,
and apply the original lifting axiom. No new existence hypothesis is used
beyond the actual localization certificate.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {C : Type u} [Category.{v} C] [original : ModelCategory C]
  [simplicial : ModelCategory SSet.{v}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfib : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{v}.rlp)

include h in
lemma replacement_unit_trivialCofibration
    (d : @LocalReplacementData C _ original simplicial cof fib S) (X : C) :
    let := original
    m.categoryWithCofibrations.cofibrations (d.η.app X) ∧
      m.categoryWithWeakEquivalences.weakEquivalences (d.η.app X) := by
  let := original
  exact ⟨h.cofibrations_eq.symm.le _ (d.unit_cofibration X),
    h.weakEquivalences_eq.symm.le _ (d.unit_localEquivalence X)⟩

include h in
lemma replacement_value_fibrant
    (d : @LocalReplacementData C _ original simplicial cof fib S) (X : C) :
    let := original
    m.categoryWithFibrations.fibrations (terminal.from (d.L.obj X)) := by
  let := original
  exact (h.fibrant_iff _).mpr (d.localFibrant X)

include h hcof hfib in
lemma fibration_of_original_of_local {X Y : C} (f : X ⟶ Y)
    (hX : @localObjects C _ original simplicial cof fib S X)
    (hY : @localFibrantObjects C _ original simplicial cof fib S Y)
    (hf : original.categoryWithFibrations.fibrations f) :
    m.categoryWithFibrations.fibrations f := by
  let := original
  let d : MorphismProperty.MapFactorizationData
      (m.categoryWithCofibrations.cofibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences)
      m.categoryWithFibrations.fibrations f := by
    let := m
    exact MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  have hZ : localFibrantObjects cof fib S d.Z := by
    apply (h.fibrant_iff d.Z).mp
    have : m.categoryWithFibrations.fibrations.IsStableUnderComposition := by
      rw [h.fibrations_eq]
      infer_instance
    have hp := m.categoryWithFibrations.fibrations.comp_mem d.p (terminal.from Y) d.hp
      ((h.fibrant_iff Y).mpr hY)
    have he : d.p ≫ terminal.from Y = terminal.from d.Z := terminal.hom_ext _ _
    exact he ▸ hp
  have hiC : cofibrations C d.i := h.cofibrations_eq.le _ d.hi.1
  have hiS : localEquivalences cof fib S d.i := h.weakEquivalences_eq.le _ d.hi.2
  have hiW : weakEquivalences C d.i :=
    (localEquivalence_iff_weakEquivalence_between_localObjects cof fib hcof hfib
      S d.i hX hZ.2).mp hiS
  have : Cofibration d.i := ⟨hiC⟩
  have : WeakEquivalence d.i := ⟨hiW⟩
  have : Fibration f := ⟨hf⟩
  have sq : CommSq (𝟙 X) d.i f d.p := ⟨by simp⟩
  have retract : RetractArrow f d.p :=
    { i := Arrow.homMk d.i (𝟙 Y) (by simp)
      r := Arrow.homMk sq.lift (𝟙 Y) }
  have : m.categoryWithFibrations.fibrations.IsStableUnderRetracts := m.cm3b
  exact MorphismProperty.of_retract retract d.hp

include h hcof hfib in
lemma fibration_iff_of_local {X Y : C} (f : X ⟶ Y)
    (hX : @localObjects C _ original simplicial cof fib S X)
    (hY : @localFibrantObjects C _ original simplicial cof fib S Y) :
    m.categoryWithFibrations.fibrations f ↔ original.categoryWithFibrations.fibrations f := by
  let := original
  exact ⟨fun hf => h.fibrations_le_original hcof f hf,
    h.fibration_of_original_of_local hcof hfib f hX hY⟩

end SerrePositivity.Bousfield.IsLocalizationModel
