module

public import SerrePositivity.CategoryTheory.Monoidal.MappingAdjunction
public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-! # Parametrized mapping adjunctions from a transported tensor action -/

@[expose] public section
universe v₁ v₂ u₁ u₂
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SerrePositivity.MonoidalMappingAdjunction
variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  {L : V ⥤ C} {R : C ⥤ V} (a : L ⊣ R)
  (H : V ⥤ C ⥤ C)
  (e : ∀ E, L ⋙ tensorRight E ≅ H.flip.obj E)
  (he : ∀ {E E' : C} (f : E' ⟶ E) (X : V),
    L.obj X ◁ f ≫ (e E).hom.app X =
      (e E').hom.app X ≫ (H.obj X).map f)

/-- A compatible family of transported tensor adjunctions is parametrized. -/
def transportedParametrizedAdjunction :
    H.flip ⊣₂ (MonoidalClosed.internalHom ⋙ (Functor.whiskeringRight C C V).obj R) := by
  refine ParametrizedAdjunction.mk' (fun E ↦ (adjunction a E).ofNatIsoLeft (e E)) ?_
  intro E E' f X F g
  exact transported_pre_bifunctor a f (e E') (e E) ((H.obj X).map f) g (he f X)

end SerrePositivity.MonoidalMappingAdjunction
