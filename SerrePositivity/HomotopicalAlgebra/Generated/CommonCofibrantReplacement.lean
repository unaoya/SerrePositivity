module

public import SerrePositivity.HomotopicalAlgebra.Generated.Replacement
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # A natural common cofibrant replacement over two trivial fibrations

For two functorial trivial fibrations to the same functor, form the actual
pullback and apply a chosen functorial cofibrant replacement. The resulting
comparison maps are natural trivial fibrations to both original functors.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.ModelReplacement.CommonCofibrant
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {B : Type u'} [Category.{v'} B]
  (d : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  {F G H : B ⥤ C} (α : F ⟶ H) (β : G ⟶ H)

abbrev raw : B ⥤ C := pullback α β

abbrev obj : B ⥤ C := raw α β ⋙ initialArrows C ⋙ d.Z

def toRaw : obj d α β ⟶ raw α β where
  app X := d.p.app (Arrow.mk (initial.to ((raw α β).obj X)))
  naturality {_ _} f := d.p.naturality ((initialArrows C).map ((raw α β).map f))

abbrev left : obj d α β ⟶ F := toRaw d α β ≫ pullback.fst α β
abbrev right : obj d α β ⟶ G := toRaw d α β ≫ pullback.snd α β

lemma over : left d α β ≫ α = right d α β ≫ β := by
  dsimp only [left, right]
  rw [Category.assoc, pullback.condition, ← Category.assoc]

lemma isCofibrant_obj (X : B) : IsCofibrant ((obj d α β).obj X) :=
  (isCofibrant_iff_of_isInitial
    (d.i.app (Arrow.mk (initial.to ((raw α β).obj X)))) initialIsInitial).mpr ⟨d.hi _⟩

lemma toRaw_trivialFibration (X : B) : trivialFibrations C ((toRaw d α β).app X) := d.hp _

lemma raw_left_trivialFibration
    (hβ : ∀ X, trivialFibrations C (β.app X)) (X : B) :
    trivialFibrations C ((pullback.fst α β).app X) :=
  (trivialFibrations C).of_isPullback
    (((IsPullback.of_hasPullback α β).map ((evaluation B C).obj X)).flip) (hβ X)

lemma raw_right_trivialFibration
    (hα : ∀ X, trivialFibrations C (α.app X)) (X : B) :
    trivialFibrations C ((pullback.snd α β).app X) :=
  (trivialFibrations C).of_isPullback
    ((IsPullback.of_hasPullback α β).map ((evaluation B C).obj X)) (hα X)

lemma left_trivialFibration
    (hβ : ∀ X, trivialFibrations C (β.app X)) (X : B) :
    trivialFibrations C ((left d α β).app X) :=
  (trivialFibrations C).comp_mem _ _ (toRaw_trivialFibration d α β X)
    (raw_left_trivialFibration α β hβ X)

lemma right_trivialFibration
    (hα : ∀ X, trivialFibrations C (α.app X)) (X : B) :
    trivialFibrations C ((right d α β).app X) :=
  (trivialFibrations C).comp_mem _ _ (toRaw_trivialFibration d α β X)
    (raw_right_trivialFibration α β hα X)

end SerrePositivity.ModelReplacement.CommonCofibrant
