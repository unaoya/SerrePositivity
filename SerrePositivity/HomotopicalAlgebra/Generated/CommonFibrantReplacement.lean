module

public import SerrePositivity.HomotopicalAlgebra.Generated.Replacement
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # A natural common fibrant replacement under two trivial cofibrations

The construction is the actual pushout followed by a chosen functorial
fibrant replacement. Both comparison maps are natural trivial cofibrations.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.ModelReplacement.CommonFibrant
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {B : Type u'} [Category.{v'} B]
  (d : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  {F G H : B ⥤ C} (α : H ⟶ F) (β : H ⟶ G)

abbrev raw : B ⥤ C := pushout α β
abbrev obj : B ⥤ C := raw α β ⋙ terminalArrows C ⋙ d.Z

def fromRaw : raw α β ⟶ obj d α β where
  app X := d.i.app (Arrow.mk (terminal.from ((raw α β).obj X)))
  naturality {_ _} f := d.i.naturality ((terminalArrows C).map ((raw α β).map f))

abbrev left : F ⟶ obj d α β := pushout.inl α β ≫ fromRaw d α β
abbrev right : G ⟶ obj d α β := pushout.inr α β ≫ fromRaw d α β

lemma under : α ≫ left d α β = β ≫ right d α β := by
  dsimp only [left, right]
  rw [← Category.assoc, pushout.condition, Category.assoc]

lemma isFibrant_obj (X : B) : IsFibrant ((obj d α β).obj X) :=
  (isFibrant_iff_of_isTerminal
    (d.p.app (Arrow.mk (terminal.from ((raw α β).obj X)))) terminalIsTerminal).mpr ⟨d.hp _⟩

lemma fromRaw_trivialCofibration (X : B) : trivialCofibrations C ((fromRaw d α β).app X) := d.hi _

lemma raw_left_trivialCofibration
    (hβ : ∀ X, trivialCofibrations C (β.app X)) (X : B) :
    trivialCofibrations C ((pushout.inl α β).app X) :=
  (trivialCofibrations C).of_isPushout
    ((IsPushout.of_hasPushout α β).map ((evaluation B C).obj X)) (hβ X)

lemma raw_right_trivialCofibration
    (hα : ∀ X, trivialCofibrations C (α.app X)) (X : B) :
    trivialCofibrations C ((pushout.inr α β).app X) :=
  (trivialCofibrations C).of_isPushout
    (((IsPushout.of_hasPushout α β).map ((evaluation B C).obj X)).flip) (hα X)

lemma left_trivialCofibration
    (hβ : ∀ X, trivialCofibrations C (β.app X)) (X : B) :
    trivialCofibrations C ((left d α β).app X) :=
  (trivialCofibrations C).comp_mem _ _ (raw_left_trivialCofibration α β hβ X)
    (fromRaw_trivialCofibration d α β X)

lemma right_trivialCofibration
    (hα : ∀ X, trivialCofibrations C (α.app X)) (X : B) :
    trivialCofibrations C ((right d α β).app X) :=
  (trivialCofibrations C).comp_mem _ _ (raw_right_trivialCofibration α β hα X)
    (fromRaw_trivialCofibration d α β X)

end SerrePositivity.ModelReplacement.CommonFibrant
