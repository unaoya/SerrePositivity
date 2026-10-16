module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation

/-! # The actual augmented free-path simplicial resolution of an arbitrary category -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreePathSimplicialResolution
variable (C : Type u) [Category.{v} C]

def diagram : SimplicialObject Cat.{max u v, u} :=
  ComonadSimplicialResolution.diagram FreePathResolution.comonad
    (FreePathResolutionPresentation.base C)

def augmentation : diagram C ⟶ (Functor.const _).obj (FreePathResolutionPresentation.base C) :=
  ComonadSimplicialResolution.augmentation FreePathResolution.comonad
    (FreePathResolutionPresentation.base C)

def projection (n : SimplexCategoryᵒᵖ) : (diagram C).obj n ⥤ C :=
  ((augmentation C).app n).toFunctor ⋙ ULiftHom.down.{v, u, u} (C := C)

lemma projection_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((diagram C).map θ).toFunctor ⋙ projection C m = projection C n := by
  have h := congrArg Cat.Hom.toFunctor ((augmentation C).naturality θ)
  change ((diagram C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor =
    ((augmentation C).app n).toFunctor at h
  change (((diagram C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor) ⋙
    ULiftHom.down.{v, u, u} (C := C) = _
  rw [h]
  rfl

lemma degree_zero : (diagram C).obj (Opposite.op (SimplexCategory.mk 0)) =
    Cat.of (Paths (ULiftHom.{u} C)) := rfl

lemma degree_one : (diagram C).obj (Opposite.op (SimplexCategory.mk 1)) =
    Cat.of (Paths (Paths (ULiftHom.{u} C))) := rfl

end SerrePositivity.HomotopyFunctionComplex.FreePathSimplicialResolution
