module

public import SerrePositivity.CategoryTheory.Limits
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! # Relative Reedy arrows as functors on the arrow category

The constructions use the same relative maps as `Objects`, and act on all
commutative squares. Thus natural arrow isomorphisms and retract diagrams
can transport Reedy conditions without choosing unrelated boundary maps.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) {C : Type u'} [Category.{v'} C]

abbrev relativeLatchingArrow (j : J) [HasColimitsOfShape (LatchingIndex r j) C]
    [HasPushouts C] : Arrow (J ⥤ C) ⥤ Arrow C :=
  RelativeArrow.pushoutFunctor (latchingComparison (C := C) r j)

abbrev relativeMatchingArrow (j : J) [HasLimitsOfShape (MatchingIndex r j) C]
    [HasPullbacks C] : Arrow (J ⥤ C) ⥤ Arrow C :=
  RelativeArrow.pullbackFunctor (matchingComparison (C := C) r j)

@[simp]
lemma relativeLatchingArrow_obj_hom (j : J) [HasColimitsOfShape (LatchingIndex r j) C]
    [HasPushouts C] {F G : J ⥤ C} (τ : F ⟶ G) :
    ((relativeLatchingArrow r j).obj (Arrow.mk τ)).hom = relativeLatchingMap r j τ := rfl

@[simp]
lemma relativeMatchingArrow_obj_hom (j : J) [HasLimitsOfShape (MatchingIndex r j) C]
    [HasPullbacks C] {F G : J ⥤ C} (τ : F ⟶ G) :
    ((relativeMatchingArrow r j).obj (Arrow.mk τ)).hom = relativeMatchingMap r j τ := rfl

section Left
variable [∀ j, HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C]
  (W : MorphismProperty C)

/-- The relative latching condition for a class W in the value category. -/
def reedyLeft : MorphismProperty (J ⥤ C) := fun _ _ τ ↦ ∀ j, W (relativeLatchingMap r j τ)

omit [∀ j, HasColimitsOfShape (LatchingIndex r j) C] in
lemma relativeLatching_iso_iff [W.RespectsIso] {F G F' G' : J ⥤ C}
    {τ : F ⟶ G} {σ : F' ⟶ G'} (e : Arrow.mk τ ≅ Arrow.mk σ) (j : J)
    [HasColimitsOfShape (LatchingIndex r j) C] :
    W (relativeLatchingMap r j τ) ↔ W (relativeLatchingMap r j σ) :=
  W.arrow_iso_iff ((relativeLatchingArrow r j).mapIso e)

instance reedyLeft_respectsIso [W.RespectsIso] : (reedyLeft r W).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (by
    intro f g e hf j
    exact (W.arrow_iso_iff ((relativeLatchingArrow r j).mapIso e)).mp (hf j))

instance reedyLeft_stableUnderRetracts [W.IsStableUnderRetracts] :
    (reedyLeft r W).IsStableUnderRetracts where
  of_retract h hg j := W.of_retract (Retract.map h (relativeLatchingArrow r j)) (hg j)

end Left

section Right
variable [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C]
  (W : MorphismProperty C)

/-- The relative matching condition for a class W in the value category. -/
def reedyRight : MorphismProperty (J ⥤ C) := fun _ _ τ ↦ ∀ j, W (relativeMatchingMap r j τ)

omit [∀ j, HasLimitsOfShape (MatchingIndex r j) C] in
lemma relativeMatching_iso_iff [W.RespectsIso] {F G F' G' : J ⥤ C}
    {τ : F ⟶ G} {σ : F' ⟶ G'} (e : Arrow.mk τ ≅ Arrow.mk σ) (j : J)
    [HasLimitsOfShape (MatchingIndex r j) C] :
    W (relativeMatchingMap r j τ) ↔ W (relativeMatchingMap r j σ) :=
  W.arrow_iso_iff ((relativeMatchingArrow r j).mapIso e)

instance reedyRight_respectsIso [W.RespectsIso] : (reedyRight r W).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (by
    intro f g e hf j
    exact (W.arrow_iso_iff ((relativeMatchingArrow r j).mapIso e)).mp (hf j))

instance reedyRight_stableUnderRetracts [W.IsStableUnderRetracts] :
    (reedyRight r W).IsStableUnderRetracts where
  of_retract h hg j := W.of_retract (Retract.map h (relativeMatchingArrow r j)) (hg j)

end Right
end SerrePositivity.Reedy
