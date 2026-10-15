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

omit [F.IsLeftAdjoint] in
/-- A single preserved latching colimit identifies the actual latching arrows. -/
def latchingComparison_preservedIso [PreservesColimit (latchingSource r j ⋙ A) F] :
    Arrow.mk ((latchingComparison r j).app (A ⋙ F)) ≅
      Arrow.mk (F.map ((latchingComparison r j).app A)) :=
  Arrow.isoMk (preservesColimitIso F (latchingSource r j ⋙ A)).symm (Iso.refl _)
    (by
      dsimp [latchingComparison]
      simp only [Category.comp_id, preservesColimitIso_inv_comp_desc]
      rfl)

/-- The left-adjoint instance supplies the required preserved colimit. -/
def latchingComparison_mapIso :
    Arrow.mk ((latchingComparison r j).app (A ⋙ F)) ≅
      Arrow.mk (F.map ((latchingComparison r j).app A)) :=
  latchingComparison_preservedIso r F A j

variable [ModelCategory C] [ModelCategory D] [SerrePositivity.Quillen.IsLeftQuillen F]

omit [F.IsLeftAdjoint] [SerrePositivity.Quillen.IsLeftQuillen F] in
/-- Preservation of the needed colimits and cofibrations is sufficient;
no ordinary right adjoint of F is required. -/
lemma reedyCofibrant_of_preservesLatching
    [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
    [∀ j, HasColimitsOfShape (LatchingIndex r j) D]
    (hF : ∀ j, PreservesColimit (latchingSource r j ⋙ A) F)
    (hcof : cofibrations C ≤ (cofibrations D).inverseImage F)
    (hA : reedyLeft r (cofibrations C) (initial.to A)) :
    reedyLeft r (cofibrations D) (initial.to (A ⋙ F)) := by
  intro j
  have := hF j
  have h : cofibrations D (F.map ((latchingComparison r j).app A)) :=
    hcof _ (latchingComparison_cofibration r j A (hA j))
  have hF : cofibrations D ((latchingComparison r j).app (A ⋙ F)) :=
    ((cofibrations D).arrow_iso_iff (latchingComparison_preservedIso r F A j)).mpr h
  exact ((cofibrations D).arrow_iso_iff (latchingInitialArrowIso r j (A ⋙ F))).mp hF

lemma reedyCofibrant_whiskerRight
    [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
    [∀ j, HasColimitsOfShape (LatchingIndex r j) D]
    (hA : reedyLeft r (cofibrations C) (initial.to A)) :
    reedyLeft r (cofibrations D) (initial.to (A ⋙ F)) :=
  reedyCofibrant_of_preservesLatching r F A (fun _ => inferInstance)
    (Quillen.IsLeftQuillen.map_cofibrations (L := F)) hA

end SerrePositivity.Reedy
