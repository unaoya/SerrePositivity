module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAugmentation

/-! # A natural bar unit through the identity-projection bar

The source is lifted only to match the base Hom universe. No model
structure or weak equivalence of this unit is assumed.
-/

@[expose] public section
universe v uD vD uB vB
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})

abbrev identityAugmentation : relative (𝟭 D) F ⟶
    F ⋙ SSet.uliftFunctor.{max uD vD, v} :=
  relativeAugmentation (𝟭 D) F (𝟙 F)

/-- The actual postcomposition of each comma chain gives the comparison component. -/
def unitComponent (d : D) :
    SSet.uliftFunctor.{vB, max uD vD v}.obj ((relative (𝟭 D) F).obj d) ⟶
      (relative p F).obj (p.obj d) where
  app n := ↾fun x => x.down ⋙ CostructuredArrow.post
    (Functor.Elements.π (F.flip.obj n)) p d
  naturality {_ _} _ := rfl

/-- Postcomposing all actual comma arrows is natural on all presentation maps. -/
def unit : relative (𝟭 D) F ⋙ SSet.uliftFunctor.{vB, max uD vD v} ⟶ p ⋙ relative p F where
  app d := unitComponent p F d
  naturality {d e} f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    change (x.down ⋙ CostructuredArrow.map f) ⋙
      CostructuredArrow.post (Functor.Elements.π (F.flip.obj n)) p e =
      (x.down ⋙ CostructuredArrow.post (Functor.Elements.π (F.flip.obj n)) p d) ⋙
        CostructuredArrow.map (p.map f)
    refine CategoryTheory.Functor.ext (fun i => congrArg
      (CostructuredArrow.mk (S := elementProjection p F n) (Y := (x.down.obj i).left))
      (p.map_comp (x.down.obj i).hom f)) ?_
    intro i j h
    apply CostructuredArrow.hom_ext
    apply Functor.Elements.hom_ext
    simp

end SerrePositivity.SimplicialModel.BarConstruction
