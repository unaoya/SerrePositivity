module

public import SerrePositivity.HomotopicalAlgebra.Localization.Fibrations
public import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion

/-! # Quillen functors out of an actual left Bousfield localization

An original Quillen adjunction extends exactly when its right adjoint
sends fibrant objects to S-local objects. The source and target Hom
universes are independent. The mapping-test condition is still defined
using the original source model.
-/

@[expose] public section
universe vC uC vD uD
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {C : Type uC} [Category.{vC} C] [original : ModelCategory C]
  [simplicial : ModelCategory SSet.{vC}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfib : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{vC}.rlp)
  {D : Type uD} [Category.{vD} D] [target : ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (hF : @Quillen.IsLeftQuillen C _ D _ original.categoryWithCofibrations
    original.categoryWithWeakEquivalences target.categoryWithCofibrations
    target.categoryWithWeakEquivalences L)

include h hcof hfib adj hF in
lemma leftQuillen_iff_rightAdjoint_local :
    @Quillen.IsLeftQuillen C _ D _ m.categoryWithCofibrations
      m.categoryWithWeakEquivalences target.categoryWithCofibrations
      target.categoryWithWeakEquivalences L ↔
    ∀ (Y : D), IsFibrant Y → @localObjects C _ original simplicial cof fib S (R.obj Y) := by
  let := original
  have : R.IsRightAdjoint := ⟨L, ⟨adj⟩⟩
  have hRo := @Quillen.isRightQuillen_of_isLeftQuillen C _ D _ original target L R adj hF
  constructor
  · intro hn Y hY
    have hRn := @Quillen.isRightQuillen_of_isLeftQuillen C _ D _ m target L R adj hn
    have hmy : m.categoryWithFibrations.fibrations (terminal.from (R.obj Y)) := by
      have hmres : m.categoryWithFibrations.fibrations.RespectsIso := by
        rw [h.fibrations_eq]
        infer_instance
      have hh := (@isFibrant_iff_of_isTerminal C _ m.categoryWithFibrations _ hmres
        _ _ (R.map (terminal.from Y))
        (terminalIsTerminal.isTerminalObj R (⊤_ D))).mpr
          ((@fibration_iff C _ _ _ (R.map (terminal.from Y)) m.categoryWithFibrations).mpr
            (hRn.map_fibrations _ ((fibration_iff _).mp hY)))
      rcases hh with ⟨hh⟩
      exact hh
    exact ((h.fibrant_iff _).mp hmy).2
  · intro hl
    apply @Quillen.isLeftQuillen_of_fibrant_test C _ m D _ target L R adj
    · intro A B i hi
      exact hF.map_cofibrations i (h.cofibrations_eq.le i hi)
    · intro X Y p hX hY hp
      have := hRo
      have : IsFibrant Y := hY
      have hRY : localFibrantObjects cof fib S (R.obj Y) :=
        ⟨Quillen.isFibrant_obj R Y, hl Y hY⟩
      exact h.fibration_of_original_of_local hcof hfib (R.map p) (hl X hX) hRY
        (hRo.map_fibrations p ((fibration_iff p).mp hp))

end SerrePositivity.Bousfield.IsLocalizationModel
