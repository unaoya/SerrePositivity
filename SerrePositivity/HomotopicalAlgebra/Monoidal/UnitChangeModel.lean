module

public import SerrePositivity.HomotopicalAlgebra.Monoidal.ModelCategory

/-! # The separate unit axiom survives enlargement of weak equivalences

Keep cofibrations fixed and enlarge the weak-equivalence class. An actual
old unit replacement still satisfies the unit axiom. The unit need not be
cofibrant, and no pushout-product axiom is inferred from this result.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MonoidalCategory

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (old m : ModelCategory C)

lemma hasUnitAxiom_change_model
    (hc : m.categoryWithCofibrations.cofibrations = old.categoryWithCofibrations.cofibrations)
    (hw : old.categoryWithWeakEquivalences.weakEquivalences ≤
      m.categoryWithWeakEquivalences.weakEquivalences)
    (hu : @HasUnitAxiom C _ old _) : @HasUnitAxiom C _ m _ := by
  let := old
  obtain ⟨Q, q, hQ⟩ := hu.exists_replacement
  have hQcof : old.categoryWithCofibrations.cofibrations (initial.to Q) :=
    (cofibration_iff _).mp hQ.cofibrant
  have hQweak : old.categoryWithWeakEquivalences.weakEquivalences q :=
    (weakEquivalence_iff _).mp hQ.weakEquivalence
  have hleft (X : C) (hX : old.categoryWithCofibrations.cofibrations (initial.to X)) :
      old.categoryWithWeakEquivalences.weakEquivalences (q ▷ X) :=
    (weakEquivalence_iff _).mp (hQ.left X ⟨hX⟩)
  have hright (X : C) (hX : old.categoryWithCofibrations.cofibrations (initial.to X)) :
      old.categoryWithWeakEquivalences.weakEquivalences (X ◁ q) :=
    (weakEquivalence_iff _).mp (hQ.right X ⟨hX⟩)
  let := m
  refine @HasUnitAxiom.mk C _ m _ ⟨Q, q, ?_⟩
  refine @UnitReplacementAxiom.mk C _ m _ Q q ?_ ?_ ?_ ?_
  · exact ⟨hc.symm.le _ hQcof⟩
  · exact ⟨hw _ hQweak⟩
  · intro X hX
    exact ⟨hw _ (hleft X (hc.le _ ((cofibration_iff _).mp hX)))⟩
  · intro X hX
    exact ⟨hw _ (hright X (hc.le _ ((cofibration_iff _).mp hX)))⟩

end SerrePositivity.Quillen
