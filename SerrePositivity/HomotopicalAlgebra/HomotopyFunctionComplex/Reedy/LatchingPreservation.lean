module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.CofibrantBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ComponentClasses
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Left adjoints preserve the actual latching comparison

The comparison is an isomorphism of arrows built from the preserved
colimit. A left Quillen left adjoint therefore sends Reedy cofibrant
objects to Reedy cofibrant objects, for arbitrary Reedy indices with
the indicated latching colimits.
-/

@[expose] public section
universe vJ uJ t vC uC vD uD
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type uJ} [Category.{vJ} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α)
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) [F.IsLeftAdjoint] (A : J ⥤ C) (j : J)
  [HasColimitsOfShape (LatchingIndex r j) C]
  [HasColimitsOfShape (LatchingIndex r j) D]

/-- The actual colimit preservation isomorphism identifies the latching arrows. -/
def latchingComparison_mapIso :
    Arrow.mk ((latchingComparison r j).app (A ⋙ F)) ≅
      Arrow.mk (F.map ((latchingComparison r j).app A)) :=
  Arrow.isoMk (preservesColimitIso F (latchingSource r j ⋙ A)).symm (Iso.refl _)
    (by
      dsimp [latchingComparison]
      simp only [Category.comp_id, preservesColimitIso_inv_comp_desc]
      rfl)

variable [ModelCategory C] [ModelCategory D] [SerrePositivity.Quillen.IsLeftQuillen F]

lemma reedyCofibrant_whiskerRight
    [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
    [∀ j, HasColimitsOfShape (LatchingIndex r j) D]
    (hA : reedyLeft r (cofibrations C) (initial.to A)) :
    reedyLeft r (cofibrations D) (initial.to (A ⋙ F)) := by
  intro j
  have h : Cofibration ((latchingComparison r j).app A) :=
    ⟨latchingComparison_cofibration r j A (hA j)⟩
  have := Quillen.map_cofibration F ((latchingComparison r j).app A)
  have hF : cofibrations D ((latchingComparison r j).app (A ⋙ F)) :=
    ((cofibrations D).arrow_iso_iff (latchingComparison_mapIso r F A j)).mpr
      ((cofibration_iff _).mp this)
  exact ((cofibrations D).arrow_iso_iff (latchingInitialArrowIso r j (A ⋙ F))).mp hF

end SerrePositivity.Reedy
