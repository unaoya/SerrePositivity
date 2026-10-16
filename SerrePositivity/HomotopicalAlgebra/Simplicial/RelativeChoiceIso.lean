module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceMaps

/-! # Isomorphisms of actual relative choice spaces

An isomorphism of targets preserving the specified boundary induces an
isomorphism of the actual pullback spaces. Entire parameter families,
including all already specified faces, are transported unchanged.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.RelativeChoiceSpace
variable {V T P Q : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q)
  (e : P ≅ Q) (he : b ≫ e.hom = b')

include he in
lemma boundary_inv : b' ≫ e.inv = b := by
  rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]

def postIso : obj i b ≅ obj i b' where
  hom := postMap i b b' e.hom he
  inv := postMap i b' b e.inv (boundary_inv b b' e he)
  hom_inv_id := by
    rw [postMap_compose]
    simpa only [e.hom_inv_id] using postMap_identity i b
  inv_hom_id := by
    rw [postMap_compose]
    simpa only [e.inv_hom_id] using postMap_identity i b'

@[reassoc (attr := simp)]
lemma postIso_hom_projection : (postIso i b b' e he).hom ≫ projection i b' = projection i b :=
  postMap_projection i b b' e.hom he

@[reassoc (attr := simp)]
lemma postIso_inv_projection : (postIso i b b' e he).inv ≫ projection i b = projection i b' :=
  postMap_projection i b' b e.inv (boundary_inv b b' e he)

lemma family_postIso_hom {K : SSet.{v}} (s : K ⟶ obj i b) :
    family i b' (s ≫ (postIso i b b' e he).hom) = family i b s ≫ e.hom :=
  family_postMap i b b' e.hom he s

lemma family_postIso_inv {K : SSet.{v}} (s : K ⟶ obj i b') :
    family i b (s ≫ (postIso i b b' e he).inv) = family i b' s ≫ e.inv :=
  family_postMap i b' b e.inv (boundary_inv b b' e he) s

lemma postIso_ofExtension (a : T ⟶ P) (ha : i ≫ a = b) :
    ofExtension i b a ha ≫ (postIso i b b' e he).hom =
      ofExtension i b' (a ≫ e.hom) (by rw [← Category.assoc, ha, he]) :=
  postMap_ofExtension i b b' e.hom he a ha

end SerrePositivity.SimplicialModel.RelativeChoiceSpace
