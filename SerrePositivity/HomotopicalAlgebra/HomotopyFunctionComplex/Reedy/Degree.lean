module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index

/-! # Degree restrictions and naturality from the two Reedy classes

Latching and matching diagrams at j depend only on objects of degree less
than deg j. Naturality on the inverse and direct classes determines
naturality on every map by the actual unique Reedy factorization.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α)

abbrev lowerProperty (a : α) : ObjectProperty J := fun j ↦ r.deg j < a
abbrev Lower (a : α) := (lowerProperty r a).FullSubcategory
abbrev lowerInclusion (a : α) : Lower r a ⥤ J := (lowerProperty r a).ι

abbrev lowerMap {a b : α} (h : a ≤ b) : Lower r a ⥤ Lower r b :=
  ObjectProperty.ιOfLE (fun _ h' ↦ lt_of_lt_of_le h' h)

abbrev latchingSourceLower (j : J) : LatchingIndex r j ⥤ Lower r (r.deg j) :=
  (lowerProperty r (r.deg j)).lift (latchingSource r j) (fun f ↦ latching_degree_lt r f)

abbrev matchingTargetLower (j : J) : MatchingIndex r j ⥤ Lower r (r.deg j) :=
  (lowerProperty r (r.deg j)).lift (matchingTarget r j) (fun f ↦ matching_degree_lt r f)

def latchingSourceLowerIso (j : J) :
    latchingSourceLower r j ⋙ lowerInclusion r (r.deg j) ≅ latchingSource r j := Iso.refl _

def matchingTargetLowerIso (j : J) :
    matchingTargetLower r j ⋙ lowerInclusion r (r.deg j) ≅ matchingTarget r j := Iso.refl _

variable {C : Type u'} [Category.{v'} C] {F G : J ⥤ C}

include r in
lemma naturality_of_reedy (app : ∀ j, F.obj j ⟶ G.obj j)
    (hinverse : ∀ {i j} (f : i ⟶ j), inverse f → F.map f ≫ app j = app i ≫ G.map f)
    (hdirect : ∀ {i j} (f : i ⟶ j), direct f → F.map f ≫ app j = app i ≫ G.map f)
    {i j : J} (f : i ⟶ j) : F.map f ≫ app j = app i ≫ G.map f := by
  obtain ⟨Z, a, b, ha, hb, hab, _⟩ := r.exists_fac f
  rw [← hab, F.map_comp, G.map_comp, Category.assoc, hdirect b hb,
    ← Category.assoc, hinverse a ha, Category.assoc]

def natTransOfReedy (app : ∀ j, F.obj j ⟶ G.obj j)
    (hinverse : ∀ {i j} (f : i ⟶ j), inverse f → F.map f ≫ app j = app i ≫ G.map f)
    (hdirect : ∀ {i j} (f : i ⟶ j), direct f → F.map f ≫ app j = app i ≫ G.map f) : F ⟶ G where
  app := app
  naturality _ _ f := naturality_of_reedy r app hinverse hdirect f

end SerrePositivity.Reedy
