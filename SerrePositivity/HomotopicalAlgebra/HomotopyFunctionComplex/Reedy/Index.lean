module

public import Mathlib.AlgebraicTopology.Reedy.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The lower-degree indexing categories for a Reedy diagram

The latching index contains nonidentity direct maps into the fixed object;
the matching index contains nonidentity inverse maps out of it. Full over
and under subcategories suffice: uniqueness of Reedy factorization forces
every intervening triangle map into the appropriate direct or inverse class.
-/

@[expose] public section
universe v u t
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α)

lemma degreeHom_of_direct {i j : J} (f : i ⟶ j) (hf : direct f) :
    r.degHom f = r.deg i :=
  r.degHom_eq (.mk i (𝟙 i) f (Category.id_comp _) (inverse.id_mem i) hf)

lemma degreeHom_of_inverse {i j : J} (f : i ⟶ j) (hf : inverse f) :
    r.degHom f = r.deg j :=
  r.degHom_eq (.mk j f (𝟙 j) (Category.comp_id _) hf (direct.id_mem j))

include r in
lemma direct_of_comp_direct {i j k : J} (f : i ⟶ j) (g : j ⟶ k)
    (h : direct (f ≫ g)) : direct f := by
  apply r.prop₂_of_degHom_eq_deg_left
  apply le_antisymm (r.degHom_le_deg_left f)
  have h' := r.degHom_comp_le_left f g
  rw [degreeHom_of_direct r _ h] at h'
  exact h'

include r in
lemma inverse_of_comp_inverse {i j k : J} (f : i ⟶ j) (g : j ⟶ k)
    (h : inverse (f ≫ g)) : inverse g := by
  apply r.prop₁_of_degHom_eq_deg_right
  apply le_antisymm (r.degHom_le_deg_right g)
  have h' := r.degHom_comp_le_right f g
  rw [degreeHom_of_inverse r _ h] at h'
  exact h'

abbrev latchingProperty (_r : ReedyStructure inverse direct α) (j : J) :
    ObjectProperty (Over j) := fun f ↦ direct f.hom ∧ ¬MorphismProperty.identities J f.hom

abbrev matchingProperty (_r : ReedyStructure inverse direct α) (j : J) :
    ObjectProperty (Under j) := fun f ↦ inverse f.hom ∧ ¬MorphismProperty.identities J f.hom

abbrev LatchingIndex (j : J) := (latchingProperty r j).FullSubcategory
abbrev MatchingIndex (j : J) := (matchingProperty r j).FullSubcategory

abbrev latchingSource (j : J) : LatchingIndex r j ⥤ J :=
  (latchingProperty r j).ι ⋙ Over.forget j

abbrev matchingTarget (j : J) : MatchingIndex r j ⥤ J :=
  (matchingProperty r j).ι ⋙ Under.forget j

lemma latching_degree_lt {j : J} (f : LatchingIndex r j) : r.deg f.obj.left < r.deg j :=
  r.lt₂ f.obj.hom f.property.1 f.property.2

lemma matching_degree_lt {j : J} (f : MatchingIndex r j) : r.deg f.obj.right < r.deg j :=
  r.lt₁ f.obj.hom f.property.1 f.property.2

lemma latching_map_direct {j : J} {f g : LatchingIndex r j} (φ : f ⟶ g) :
    direct φ.hom.left :=
  direct_of_comp_direct r _ g.obj.hom (by rw [Over.w]; exact f.property.1)

lemma matching_map_inverse {j : J} {f g : MatchingIndex r j} (φ : f ⟶ g) :
    inverse φ.hom.right :=
  inverse_of_comp_inverse r f.obj.hom _ (by rw [Under.w]; exact g.property.1)

lemma latching_isEmpty_of_isMin {j : J} (hj : IsMin (r.deg j)) :
    IsEmpty (LatchingIndex r j) := ⟨fun f ↦ (hj.not_lt (latching_degree_lt r f)).elim⟩

lemma matching_isEmpty_of_isMin {j : J} (hj : IsMin (r.deg j)) :
    IsEmpty (MatchingIndex r j) := ⟨fun f ↦ (hj.not_lt (matching_degree_lt r f)).elim⟩

end SerrePositivity.Reedy
