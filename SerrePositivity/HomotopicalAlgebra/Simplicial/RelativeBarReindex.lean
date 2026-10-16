module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarConstruction

/-! # Actual relative bar maps induced by reindexing

The two index categories share object and Hom universes; the base and value
universes remain independent. All chains and labels are transported by the
actual functor. No weak equivalence or cofinality assumption is needed.
-/

@[expose] public section
universe v uI vI uB vB
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {E D : Type uI} [Category.{vI} E] [Category.{vI} D]
  {B : Type uB} [Category.{vB} B] (q : E ⥤ D) (p : D ⥤ B) (F : D ⥤ SSet.{v})

abbrev reindexComma (b : B) (n : SimplexCategoryᵒᵖ) :
    CostructuredArrow (elementProjection (q ⋙ p) (q ⋙ F) n) b ⥤
      CostructuredArrow (elementProjection p F n) b :=
  CostructuredArrow.pre (Functor.Elements.precomp q (F.flip.obj n)) (elementProjection p F n) b

def reindexComponent (b : B) : (relative (q ⋙ p) (q ⋙ F)).obj b ⟶ (relative p F).obj b where
  app n := ↾fun c => c ⋙ reindexComma q p F b n
  naturality {_ _} _ := rfl

/-- Reindexing is natural in the original base category before localization. -/
def reindex : relative (q ⋙ p) (q ⋙ F) ⟶ relative p F where
  app := reindexComponent q p F
  naturality {_ _} _ := rfl

end SerrePositivity.SimplicialModel.BarConstruction
