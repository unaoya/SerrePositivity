module

public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.CategoryTheory.Equivalence

/-! # Projective lifting classes under equivalence of index categories

This uses only the adjunction between the two reindexing functors.
There is no model structure or presentability assumption on the target.
-/

@[expose] public section
universe vK uK vL uL v u
noncomputable section
open CategoryTheory

namespace SerrePositivity.DiagramModel.ProjectiveReindexing
variable {K : Type uK} [Category.{vK} K] {L : Type uL} [Category.{vL} L]
  {C : Type u} [Category.{v} C]

lemma llp_map (e : K ≌ L) (Q : MorphismProperty C) {F G : K ⥤ C} (a : F ⟶ G)
    (ha : (Q.functorCategory K).llp a) :
    (Q.functorCategory L).llp (Functor.whiskerLeft e.inverse a) := by
  intro U V p hp
  have h := ha ((e.congrLeft (E := C)).inverse.map p)
    (fun k => hp (e.functor.obj k))
  exact ((e.congrLeft (E := C)).toAdjunction.hasLiftingProperty_iff a p).mpr h

end SerrePositivity.DiagramModel.ProjectiveReindexing
