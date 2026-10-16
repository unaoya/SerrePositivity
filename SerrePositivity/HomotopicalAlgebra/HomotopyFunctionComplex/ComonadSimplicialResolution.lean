module

public import SerrePositivity.CategoryTheory.Simplex.PresentationEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionPresentation
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-! # The augmented simplicial resolution of an arbitrary comonad

The index here is the usual simplex category. The comparison with the
presented simplex category is proved in PresentationEquivalence.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.ComonadSimplicialResolution
variable {C : Type u} [Category.{v} C] (G : Comonad C) (X : C)

def diagram : SimplicialObject C :=
  SimplexPresentation.inverse.op ⋙ ComonadResolutionPresentation.diagram G X

lemma diagram_obj (n : ℕ) :
    (diagram G X).obj (Opposite.op (SimplexCategory.mk n)) =
      ComonadResolutionOperators.power G X (n + 1) := rfl

lemma diagram_face {n : ℕ} (i : Fin (n + 2)) :
    (diagram G X).δ i = ComonadResolutionOperators.face G X (n + 1) i := by
  change (ComonadResolutionPresentation.diagram G X).map
    (SimplexPresentation.inverse.map (SimplexCategory.δ i)).op = _
  rw [SimplexPresentation.inverse_face]
  exact ComonadResolutionPresentation.diagram_face G X i

lemma diagram_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    (diagram G X).σ i = ComonadResolutionOperators.degeneracy G X n i := by
  change (ComonadResolutionPresentation.diagram G X).map
    (SimplexPresentation.inverse.map (SimplexCategory.σ i)).op = _
  rw [SimplexPresentation.inverse_degeneracy]
  exact ComonadResolutionPresentation.diagram_degeneracy G X i

def augmentation : diagram G X ⟶ (Functor.const _).obj X :=
  Functor.whiskerLeft SimplexPresentation.inverse.op
    (ComonadResolutionPresentation.augmentationNatTrans G X)

lemma augmentation_app (n : ℕ) :
    (augmentation G X).app (Opposite.op (SimplexCategory.mk n)) =
      ComonadResolutionOperators.augmentation G X (n + 1) := rfl

end SerrePositivity.HomotopyFunctionComplex.ComonadSimplicialResolution
