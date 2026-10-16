module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-! # A model-free strict bar candidate on the undecorated base category

For p : D → B and F : D → SSet, use the nerves of degreewise element
categories over p(d) → b. The result is strictly functorial in b. Its
values may lie in the index universe; no smallness or weak equivalence
claim is built into the construction.
-/

@[expose] public section
universe v uD vD uB vB
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})

abbrev elementProjection (n : SimplexCategoryᵒᵖ) : (F.flip.obj n).Elements ⥤ B :=
  Functor.Elements.π (F.flip.obj n) ⋙ p

/-- The two directions of the bar diagram are actual simplicial and base functor maps. -/
def commaLevels : SimplexCategoryᵒᵖ ⥤ B ⥤ Cat.{vD, max uD v vB} where
  obj n := CostructuredArrow.functor (elementProjection p F n)
  map {n m} θ := CostructuredArrow.preFunctor ((F.flip.map θ).mapElements)
    (elementProjection p F m)
  map_id n := by
    rw [F.flip.map_id]
    rfl
  map_comp θ σ := by
    rw [F.flip.map_comp]
    rfl

/-- A strict base functor built by ordinary nerves and the actual bisimplicial diagonal. -/
abbrev relative : B ⥤ SSet.{max uD vD v vB} :=
  (commaLevels p F).flip ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ Cat.{vD, max uD v vB}
      SSet.{max uD vD v vB}).obj nerveFunctor ⋙
    SerrePositivity.BisimplicialModel.diagonal

lemma relative_obj_degree (b : B) (n : SimplexCategoryᵒᵖ) :
    ((relative p F).obj b).obj n =
      ComposableArrows (CostructuredArrow (elementProjection p F n) b) n.unop.len := rfl

lemma relative_map_degree {b c : B} (f : b ⟶ c) (n : SimplexCategoryᵒᵖ)
    (x : ComposableArrows (CostructuredArrow (elementProjection p F n) b) n.unop.len) :
    ((relative p F).map f).app n x = x ⋙ CostructuredArrow.map f := rfl

end SerrePositivity.SimplicialModel.BarConstruction
