module

public import SerrePositivity.CategoryTheory.Presentation.RetractWordMap
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterCategory
public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordRetractionAction

/-! # Actual degreewise evaluation of the word presentation from strong contractions

Every defining relation is checked using the actual word action. No model
structure, additional coherence witness, or evaluation-kernel quotient is used.
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.WordPresentationRealization

def parameterEvaluation {T : SSet.{v}} (n : SimplexCategoryᵒᵖ) (t : T.obj n) :
    ParameterCategory.Object T ⥤ Type v where
  obj X := X.value.obj n
  map f := ↾fun x => f.app n (x, t)
  map_id _ := rfl
  map_comp _ _ := rfl

variable {C : Type u} [Category.{w} C] {T : SSet.{v}}
  (F : C ⥤ ParameterCategory.Object T) (K : C → SSet.{v})
  (s : ∀ X, K X ⟶ (F.obj X).value) (p : ∀ X, (F.obj X).value ⟶ K X)
  (hs : ∀ X, s X ≫ p X = 𝟙 (K X))
  (H : ∀ X, SSet.Homotopy (𝟙 (F.obj X).value) (p X ≫ s X))
  (hP : ∀ X, (H X).h ≫ p X = fst (F.obj X).value WordSegment.interval ≫ p X)
  (hS : ∀ X, s X ▷ WordSegment.interval ≫ (H X).h = fst (K X) WordSegment.interval ≫ s X)

def realization (n : SimplexCategoryᵒᵖ) (t : T.obj n) :
    RetractWords.Realization C (WordSegment.degree n) (Type v) where
  ambient := F ⋙ parameterEvaluation n t
  small X := (K X).obj n
  section_ X := (s X).app n
  projection X := (p X).app n
  action X w := ↾fun x => WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n w x
  action_one X := by
    apply ConcreteCategory.hom_ext
    intro x
    change WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n 1 x = x
    rw [map_one, RetractEndomorphisms.one_apply]
  action_mul X a b := by
    apply ConcreteCategory.hom_ext
    intro x
    change WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n (a * b) x = _
    rw [map_mul]
    rfl
  split X := congr_app (hs X) n
  action_zero X := by
    apply ConcreteCategory.hom_ext
    intro x
    change WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n 0 x = _
    rw [map_zero, RetractEndomorphisms.zero_apply]
    rfl
  section_action X w := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n w).fixed x
  action_projection X w := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n w).over x

abbrev functor (n : SimplexCategoryᵒᵖ) (t : T.obj n) :=
  (realization F K s p hs H hP hS n t).functor

abbrev smallFunctor (n : SimplexCategoryᵒᵖ) (t : T.obj n) :=
  (realization F K s p hs H hP hS n t).smallFunctor

end SerrePositivity.SimplicialModel.WordPresentationRealization
