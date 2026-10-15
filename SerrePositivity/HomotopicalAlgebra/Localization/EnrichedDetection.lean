module

public import SerrePositivity.HomotopicalAlgebra.Localization.EnrichedLocalObjects
public import SerrePositivity.HomotopicalAlgebra.Localization.EnrichedTestComparison

/-! # Ordinary and V-enriched localizations agree under action compatibility

The old action unit axiom gives enriched tests ⇒ ordinary tests. The
proved localized tensor axiom gives the reverse implication for local
targets and local equivalences. Thus both the local-object predicates
and the two weak-equivalence classes agree, as actual equalities.
-/

@[expose] public section
universe vV uV vC uC
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [base : ModelCategory V]
  {C : Type uC} [Category.{vC} C] [original : ModelCategory C]
  [EnrichedOrdinaryCategory V C] [simplicial : ModelCategory SSet.{vC}]
  [ModelCategory SSet.{vV}] [ModelCategory SSet.{max vC vV}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcofC : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfibC : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{vC}.rlp)
  (P : SerrePositivity.Enriched.TensorCotensor V C)
  (hP : @Quillen.IsQuillenBifunctor V _ base C _ original C _ original P.tensor)
  (hPn : @Quillen.IsQuillenBifunctor V _ base C _ m C _ m P.tensor)
  (hunit : let := original; SerrePositivity.Enriched.HasTensorUnitAxiom P)
  (cofV : MorphismProperty.FunctorialFactorizationData (cofibrations V) (trivialFibrations V))
  (hcofV : cofibrations SSet.{vV} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{vV} = SSet.modelCategoryQuillen.J.{vV}.rlp)
  (hcofB : cofibrations SSet.{max vC vV} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max vC vV} = SSet.modelCategoryQuillen.J.{max vC vV}.rlp)

include h hcofC hfibC P hP hPn hunit cofV hcofV hfibV hcofB hfibB in
lemma localObjects_eq_enriched :
    let := original
    Bousfield.localObjects.{vC, uC} (C := C) cof fib S =
      SerrePositivity.Enriched.localObjects (V := V) cof fib S := by
  let := original
  have : Quillen.IsQuillenBifunctor P.tensor := hP
  have : SerrePositivity.Enriched.HasTensorUnitAxiom P := hunit
  change Bousfield.localObjects.{vC, uC} (C := C) cof fib S =
    SerrePositivity.Enriched.localObjects (V := V) cof fib S
  funext Y
  apply propext
  exact ⟨h.enrichedLocalObjects_of_localObjects hcofC P hPn Y,
    localObjects_of_enrichedLocalObjects P cofV cof fib hcofC hfibC hcofV hfibV hcofB hfibB S Y⟩

include h hcofC hfibC P hP hPn hunit cofV hcofV hfibV hcofB hfibB in
lemma localEquivalences_eq_enriched :
    let := original
    Bousfield.localEquivalences.{vC, uC} (C := C) cof fib S =
      SerrePositivity.Enriched.localEquivalences (V := V) cof fib S := by
  let := original
  have : Quillen.IsQuillenBifunctor P.tensor := hP
  have : SerrePositivity.Enriched.HasTensorUnitAxiom P := hunit
  have ho := h.localObjects_eq_enriched (V := V) hcofC hfibC P hP hPn hunit cofV
    hcofV hfibV hcofB hfibB
  change Bousfield.localEquivalences.{vC, uC} (C := C) cof fib S =
    SerrePositivity.Enriched.localEquivalences (V := V) cof fib S
  ext X Z f
  constructor
  · intro hf Y hY
    have hYo := (congrArg (fun T : C → Prop => T Y) ho).mpr hY
    exact h.enrichedMappingTest_of_localEquivalence hcofC P hPn f hf Y hYo
  · intro hf Y hY
    have hYe := (congrArg (fun T : C → Prop => T Y) ho).mp hY
    exact mappingTest_of_enrichedTest P cofV cof fib hcofC hfibC hcofV hfibV hcofB hfibB f Y
      (hf Y hYe)

include h hcofC hfibC P hP hPn hunit cofV hcofV hfibV hcofB hfibB in
lemma fibrant_iff_enriched (Y : C) :
    let := original
    m.categoryWithFibrations.fibrations (terminal.from Y) ↔ IsFibrant Y ∧
      SerrePositivity.Enriched.localObjects (V := V) cof fib S Y := by
  let := original
  have ho := h.localObjects_eq_enriched (V := V) hcofC hfibC P hP hPn hunit cofV
    hcofV hfibV hcofB hfibB
  exact (h.fibrant_iff Y).trans (and_congr Iff.rfl
    (congrArg (fun T : C → Prop => T Y) ho).to_iff)

end SerrePositivity.Bousfield.IsLocalizationModel
