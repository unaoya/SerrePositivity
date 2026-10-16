module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies
public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationRealization

/-! # Actual presented word-category evaluation on the ordinary bar retracts

All free-resolution degrees are included. The small evaluation lands in the
original value universe, while the source presented category may be larger.
This is not yet an action on the original base category.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordPresentation
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ) (k : SimplexCategoryᵒᵖ) (t : (parameters P n).obj k)

abbrev realization :=
  WordPresentationRealization.realization
    (OrdinaryBarFreeAmbientFamilies.fixedAction (C := C) hcof hfib P n)
    (lifted (C := C) hcof hfib) (section_ (C := C) hcof hfib)
    (projection (C := C) hcof hfib) (section_fac (C := C) hcof hfib)
    (contraction (C := C) hcof hfib) (contraction_over (C := C) hcof hfib)
    (contraction_on_section (C := C) hcof hfib) k t

abbrev largeEvaluation := (realization (C := C) hcof hfib P n k t).functor
abbrev smallLiftedEvaluation := (realization (C := C) hcof hfib P n k t).smallFunctor

abbrev smallCategory := RetractWords.Small (degree (D C) (n + 1)) (WordSegment.degree.{max u v} k)

def smallEvaluation : smallCategory (C := C) n k ⥤ Type v where
  obj X := (small hcof hfib X).obj k
  map f := ↾fun x => ((smallLiftedEvaluation (C := C) hcof hfib P n k t).map f (ULift.up x)).down
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    change ((smallLiftedEvaluation (C := C) hcof hfib P n k t).map (𝟙 X) (ULift.up x)).down = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    change ((smallLiftedEvaluation (C := C) hcof hfib P n k t).map (f ≫ g) (ULift.up x)).down = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

lemma smallEvaluation_obj (X : smallCategory (C := C) n k) :
    (smallEvaluation hcof hfib P n k t).obj X = (small hcof hfib X).obj k := rfl

lemma smallEvaluation_map (X Y : smallCategory (C := C) n k) (f : X ⟶ Y)
    (x : (small hcof hfib X).obj k) :
    (smallEvaluation hcof hfib P n k t).map f x =
      ((smallLiftedEvaluation (C := C) hcof hfib P n k t).map f (ULift.up x)).down := rfl

lemma largeEvaluation_transferred {X Y : degree (D C) (n + 1)} (f : X ⟶ Y) :
    (largeEvaluation (C := C) hcof hfib P n k t).map
      ((RetractWords.quotient (degree (D C) (n + 1)) (WordSegment.degree.{max u v} k)).map
        (RetractWords.section_ _ _ X ≫ RetractWords.source _ _ f ≫
          RetractWords.projection _ _ Y)) =
      (section_ hcof hfib X).app k ≫
        (WordPresentationRealization.parameterEvaluation k t).map
          (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f) ≫
        (projection hcof hfib Y).app k := by
  simp only [CategoryTheory.Functor.map_comp, RetractWords.Realization.functor_section,
    RetractWords.Realization.functor_source, RetractWords.Realization.functor_projection]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordPresentation
