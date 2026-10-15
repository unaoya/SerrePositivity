module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Latching maps of a Reedy cofibrant object

The initial diagram has initial latching object and initial components.
Thus its latching comparison is an isomorphism and the relative initial
latching arrow is isomorphic to the absolute latching comparison of A.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)
  {C : Type u'} [Category.{v'} C] [ModelCategory C]
  [HasColimitsOfShape (LatchingIndex r j) C]

lemma latchingComparison_initial_isIso :
    IsIso ((latchingComparison r j).app (⊥_ (J ⥤ C))) :=
  isIso_of_isInitial
    (initialIsInitial.isInitialObj (latchingEvaluation r j) (⊥_ (J ⥤ C)))
    (initialIsInitial.isInitialObj ((evaluation J C).obj j) (⊥_ (J ⥤ C))) _

def latchingInitialArrowIso (A : J ⥤ C) :
    Arrow.mk ((latchingComparison r j).app A) ≅
      Arrow.mk (relativeLatchingMap r j (initial.to A)) := by
  have := latchingComparison_initial_isIso (C := C) r j
  exact Arrow.isoMk (asIso (pushout.inl ((latchingEvaluation r j).map (initial.to A))
    ((latchingComparison r j).app (⊥_ (J ⥤ C))))) (Iso.refl _)
      ((inl_relativeLatchingMap r j (initial.to A)).trans
        (Category.comp_id ((latchingComparison r j).app A)).symm)

lemma latchingComparison_cofibration (A : J ⥤ C)
    (hA : cofibrations C (relativeLatchingMap r j (initial.to A))) :
    cofibrations C ((latchingComparison r j).app A) :=
  ((cofibrations C).arrow_iso_iff (latchingInitialArrowIso r j A)).mpr hA

end SerrePositivity.Reedy
