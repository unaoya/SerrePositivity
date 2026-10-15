module

public import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantTesting
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # An adjunction is Quillen by testing fibrations between fibrant objects

Cofibration preservation and preservation by the right adjoint of
fibrations between fibrant objects suffice. The weak-equivalence test is
proved in `FibrantTesting`; no properness or presentation assumptions enter.
-/

@[expose] public section
universe vC uC vD uD
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

include adj in
lemma isLeftQuillen_of_fibrant_test
    (hcof : cofibrations C ≤ (cofibrations D).inverseImage L)
    (hfib : ∀ {X Y : D} (p : X ⟶ Y), IsFibrant X → IsFibrant Y →
      Fibration p → fibrations C (R.map p)) : IsLeftQuillen L := by
  refine ⟨hcof, ?_⟩
  intro A B i hi
  have : Cofibration i := ⟨hi.1⟩
  have : WeakEquivalence i := ⟨hi.2⟩
  refine ⟨hcof i hi.1, weakEquivalence_of_lifts_fibrant_fibrations (L.map i) ?_⟩
  intro X Y p hX hY hp
  have : Fibration (R.map p) := ⟨hfib p hX hY hp⟩
  exact (adj.hasLiftingProperty_iff i p).mpr inferInstance

include adj in
lemma isLeftQuillen_iff_fibrant_test : IsLeftQuillen L ↔
    (cofibrations C ≤ (cofibrations D).inverseImage L) ∧
      ∀ {X Y : D} (p : X ⟶ Y), IsFibrant X → IsFibrant Y →
        Fibration p → fibrations C (R.map p) := by
  constructor
  · intro h
    have := h
    have := isRightQuillen_of_isLeftQuillen adj
    exact ⟨h.map_cofibrations, fun p _ _ hp => IsRightQuillen.map_fibrations p
      ((fibration_iff p).mp hp)⟩
  · rintro ⟨hc, hf⟩
    exact isLeftQuillen_of_fibrant_test adj hc hf


lemma isFibrant_obj (R : D ⥤ C) [R.IsRightAdjoint] [IsRightQuillen R]
    (Y : D) [IsFibrant Y] : IsFibrant (R.obj Y) := by
  have : Fibration (R.map (Limits.terminal.from Y)) := map_fibration R _
  exact (isFibrant_iff_of_isTerminal (R.map (Limits.terminal.from Y))
    (Limits.terminalIsTerminal.isTerminalObj R (⊤_ D))).mpr inferInstance

end SerrePositivity.Quillen
