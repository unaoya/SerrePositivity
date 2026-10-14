module

public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Colimit morphism properties over thin groupoids

A groupoid with at most one morphism between any two objects is equivalent to
its discrete set of connected components. Thus a morphism class stable under
coproducts is stable under these colimits. This accounts for the freeness of
induction indexing categories without treating arbitrary orbit quotients as
coproducts.
-/

@[expose] public section
universe u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.ThinGroupoid
variable {J : Type u} [Category.{v} J] [IsGroupoid J]

lemma nonempty_hom_of_zigzag {X Y : J} (h : Zigzag X Y) : Nonempty (X ⟶ Y) := by
  induction h with
  | refl => exact ⟨𝟙 _⟩
  | tail _ hz ih =>
    obtain ⟨f⟩ := ih
    rcases hz with hg | hg
    · obtain ⟨g⟩ := hg
      exact ⟨f ≫ g⟩
    · obtain ⟨g⟩ := hg
      exact ⟨f ≫ inv g⟩

/-- The projection onto connected components, as a discrete category. -/
def componentProjection : J ⥤ Discrete (ConnectedComponents J) :=
  ConnectedComponents.functorToDiscrete _ id

instance [Quiver.IsThin J] : (componentProjection (J := J)).Faithful where
  map_injective := fun _ ↦ Subsingleton.elim _ _

instance : (componentProjection (J := J)).Full where
  map_surjective {X Y} f := by
    have h : Quotient.mk (Zigzag.setoid J) X = Quotient.mk (Zigzag.setoid J) Y :=
      Discrete.eq_of_hom f
    exact ⟨(nonempty_hom_of_zigzag (Quotient.exact h)).some, Subsingleton.elim _ _⟩

instance : (componentProjection (J := J)).EssSurj where
  mem_essImage q := by
    obtain ⟨X, hX⟩ := Quotient.exists_rep q.as
    exact ⟨X, ⟨eqToIso (Discrete.ext hX)⟩⟩

instance [Quiver.IsThin J] : (componentProjection (J := J)).IsEquivalence where

/-- Choice-independent at the projection level; the selected inverse is the
ordinary Mathlib inverse of a fully faithful essentially surjective functor. -/
def discreteEquivalence [Quiver.IsThin J] : J ≌ Discrete (ConnectedComponents J) :=
  (componentProjection (J := J)).asEquivalence

variable {C : Type u'} [Category.{v'} C] (P : MorphismProperty C)

lemma colimitsOfShape_le [Quiver.IsThin J]
    [P.IsStableUnderCoproductsOfShape (ConnectedComponents J)] : P.colimitsOfShape J ≤ P := by
  rw [P.colimitsOfShape_eq_of_equivalence (discreteEquivalence (J := J))]
  exact P.colimitsOfShape_le

lemma isStableUnderColimitsOfShape [Quiver.IsThin J]
    [P.IsStableUnderCoproductsOfShape (ConnectedComponents J)] :
    P.IsStableUnderColimitsOfShape J :=
  (P.isStableUnderColimitsOfShape_iff_colimitsOfShape_le J).2 (colimitsOfShape_le P)
end SerrePositivity.ThinGroupoid
