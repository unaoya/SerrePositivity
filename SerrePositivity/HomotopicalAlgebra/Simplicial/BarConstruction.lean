module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction
public import Mathlib.CategoryTheory.Elements
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # A model-free bar functor with independent index and value universes

Take the nerve of the category of elements at each simplicial degree and
then its bisimplicial diagonal. Values may grow with the index universe.
No model structure is imposed in that larger universe.
-/

@[expose] public section
universe v uD vD
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable (D : Type uD) [Category.{vD} D]

/-- Rows are the actual nerves of categories of degreewise elements. -/
abbrev rows : (D ⥤ SSet.{v}) ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{max uD vD v}) :=
  flipFunctor D SimplexCategoryᵒᵖ (Type v) ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ (D ⥤ Type v)
      Cat.{vD, max uD v}).obj Functor.elementsFunctor ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ Cat.{vD, max uD v}
      SSet.{max uD vD v}).obj nerveFunctor

/-- The Bousfield--Kan simplicial replacement, functorial in the whole input diagram. -/
abbrev functor : (D ⥤ SSet.{v}) ⥤ SSet.{max uD vD v} :=
  rows D ⋙ SerrePositivity.BisimplicialModel.diagonal

lemma obj_degree (F : D ⥤ SSet.{v}) (n : SimplexCategoryᵒᵖ) :
    ((functor D).obj F).obj n =
      ComposableArrows ((F.flip.obj n).Elements) n.unop.len := rfl

lemma map_degree {F G : D ⥤ SSet.{v}} (a : F ⟶ G) (n : SimplexCategoryᵒᵖ)
    (c : ComposableArrows ((F.flip.obj n).Elements) n.unop.len) :
    ((functor D).map a).app n c =
      c ⋙ ((Functor.whiskerRight a ((evaluation SimplexCategoryᵒᵖ (Type v)).obj n)).mapElements) :=
  rfl

end SerrePositivity.SimplicialModel.BarConstruction
