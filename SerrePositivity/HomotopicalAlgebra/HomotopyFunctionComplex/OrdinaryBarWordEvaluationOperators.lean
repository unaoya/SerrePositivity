module

public import SerrePositivity.CategoryTheory.Presentation.RetractWordExt
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationSourceMap

/-! # All free-resolution faces and degeneracies commute with the actual word evaluation -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem OrdinaryBarWordPresentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ)

lemma evaluation_face (i : Fin (n + 2)) (k : SimplexCategoryᵒᵖ) (t : (parameters P n).obj k) :
    RetractWords.map (FreeGeneratorFaces.fixedFace (D C) (n + 1) i)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k)) ⋙
      largeEvaluation (C := C) hcof hfib P n k t =
    largeEvaluation (C := C) hcof hfib P (n + 1) k ((P ◁ SSet.stdSimplex.δ i).app k t) := by
  apply RetractWords.functor_ext_generators
    (C := degree (D C) (n + 2)) (M := WordSegment.degree.{max u v} k)
  · rintro ⟨X⟩
    cases X <;> rfl
  · intro X Y e
    change RetractWords.Edge _ _ X Y at e
    cases e with
    | source f =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_source,
        RetractWords.Realization.functor_source]
      apply heq_of_eq
      apply ConcreteCategory.hom_ext
      intro x
      change (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n
        ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).map f)).app k (x, t) =
          (OrdinaryBarFreeAmbientFamilies.family hcof hfib P (n + 1) f).app k
            (x, (P ◁ SSet.stdSimplex.δ i).app k t)
      exact (types_congr_hom (congr_app
        (OrdinaryBarFreeAmbientFamilies.family_face hcof hfib P n i f) k) (x, t)).symm
    | word X w =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_word,
        RetractWords.Realization.functor_word]
      rfl
    | section_ X =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_section,
        RetractWords.Realization.functor_section]
      rfl
    | projection X =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_projection,
        RetractWords.Realization.functor_projection]
      rfl

lemma evaluation_degeneracy (i : Fin (n + 1)) (k : SimplexCategoryᵒᵖ)
    (t : (parameters P (n + 1)).obj k) :
    RetractWords.map (degeneracyFunctor (D C) n i)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k)) ⋙
      largeEvaluation (C := C) hcof hfib P (n + 1) k t =
    largeEvaluation (C := C) hcof hfib P n k
      ((P ◁ OrdinaryBarFreeResolutionDegeneracyValues.sigma n i).app k t) := by
  apply RetractWords.functor_ext_generators
    (C := degree (D C) (n + 1)) (M := WordSegment.degree.{max u v} k)
  · rintro ⟨X⟩
    cases X <;> rfl
  · intro X Y e
    change RetractWords.Edge _ _ X Y at e
    cases e with
    | source f =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_source,
        RetractWords.Realization.functor_source]
      apply heq_of_eq
      apply ConcreteCategory.hom_ext
      intro x
      change (OrdinaryBarFreeAmbientFamilies.family hcof hfib P (n + 1)
        ((degeneracyFunctor (D C) n i).map f)).app k (x, t) =
          (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f).app k
            (x, (P ◁ OrdinaryBarFreeResolutionDegeneracyValues.sigma n i).app k t)
      exact types_congr_hom (congr_app
        (OrdinaryBarFreeAmbientFamilies.family_degeneracy hcof hfib P n i f) k) (x, t)
    | word X w =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_word,
        RetractWords.Realization.functor_word]
      rfl
    | section_ X =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_section,
        RetractWords.Realization.functor_section]
      rfl
    | projection X =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_projection,
        RetractWords.Realization.functor_projection]
      rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators
