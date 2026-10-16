module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionPresentation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolution
public import Mathlib.CategoryTheory.Category.ULift

/-! # The augmented free-path diagram in all degrees, with independent universes

Only Hom is explicitly lifted to place the original category in Cat. The
index is the presented simplex category; its equivalence with the usual
simplex category is not assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreePathResolutionPresentation
variable (C : Type u) [Category.{v} C]

abbrev base : Cat.{max u v, u} := Cat.of (ULiftHom.{u} C)

def diagram : SimplexCategoryGenRelᵒᵖ ⥤ Cat.{max u v, u} :=
  ComonadResolutionPresentation.diagram FreePathResolution.comonad (base C)

def augmentation : diagram C ⟶ (Functor.const _).obj (base C) :=
  ComonadResolutionPresentation.augmentationNatTrans FreePathResolution.comonad (base C)

def projection (n : SimplexCategoryGenRelᵒᵖ) : (diagram C).obj n ⥤ C :=
  ((augmentation C).app n).toFunctor ⋙ ULiftHom.down.{v, u, u} (C := C)

lemma projection_naturality {n m : SimplexCategoryGenRelᵒᵖ} (θ : n ⟶ m) :
    ((diagram C).map θ).toFunctor ⋙ projection C m = projection C n := by
  have h := congrArg Cat.Hom.toFunctor ((augmentation C).naturality θ)
  change ((diagram C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor =
    ((augmentation C).app n).toFunctor at h
  change (((diagram C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor) ⋙
    ULiftHom.down.{v, u, u} (C := C) = _
  rw [h]
  rfl

lemma degree_zero : (diagram C).obj (Opposite.op (SimplexCategoryGenRel.mk 0)) =
    Cat.of (Paths (ULiftHom.{u} C)) := rfl

lemma degree_one : (diagram C).obj (Opposite.op (SimplexCategoryGenRel.mk 1)) =
    Cat.of (Paths (Paths (ULiftHom.{u} C))) := rfl

end SerrePositivity.HomotopyFunctionComplex.FreePathResolutionPresentation
