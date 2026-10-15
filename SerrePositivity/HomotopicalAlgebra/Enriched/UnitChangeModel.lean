module

public import SerrePositivity.HomotopicalAlgebra.Enriched.UnitAxiom

/-! # The action unit axiom survives ordinary localization

Keep cofibrations in C fixed and enlarge its weak equivalences. The same
actual unit replacement in V then satisfies the enriched action's unit
axiom. No cofibrancy of the enriching unit is imposed.
-/

@[expose] public section
universe vV uV vC uC
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Enriched
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [base : ModelCategory V]
  {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  (old m : ModelCategory C) (P : TensorCotensor V C)

lemma hasTensorUnitAxiom_change_model
    (hc : m.categoryWithCofibrations.cofibrations = old.categoryWithCofibrations.cofibrations)
    (hw : old.categoryWithWeakEquivalences.weakEquivalences ≤
      m.categoryWithWeakEquivalences.weakEquivalences)
    (hu : @HasTensorUnitAxiom V _ _ base C _ old _ P) :
    @HasTensorUnitAxiom V _ _ base C _ m _ P := by
  let := old
  obtain ⟨U, q, hU⟩ := hu.exists_replacement
  have hcof := hU.cofibrant
  have hweak := hU.weakEquivalence
  have htensor (X : C) (hX : old.categoryWithCofibrations.cofibrations (initial.to X)) :
      old.categoryWithWeakEquivalences.weakEquivalences
        ((P.tensor.map q).app X ≫ P.unitMap X) := hU.tensor X ⟨hX⟩
  let := m
  refine @HasTensorUnitAxiom.mk V _ _ base C _ m _ P ⟨U, q, ?_⟩
  refine @TensorUnitReplacementAxiom.mk V _ _ base C _ m _ P U q hcof hweak ?_
  intro X hX
  exact hw _ (htensor X (hc.le _ ((cofibration_iff _).mp hX)))

end SerrePositivity.Enriched
