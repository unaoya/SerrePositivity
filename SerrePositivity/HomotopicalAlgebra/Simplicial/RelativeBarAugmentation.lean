module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarConstruction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLift

/-! # Natural augmentation of the strict relative bar along an actual comparison diagram -/

@[expose] public section
universe v uD vD uB vB
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v}) {G : B ⥤ SSet.{v}} (a : F ⟶ p ⋙ G)

abbrev label (b : B) (n : SimplexCategoryᵒᵖ)
    (e : CostructuredArrow (elementProjection p F n) b) : (G.obj b).obj n :=
  (G.map e.hom).app n ((a.app e.left.obj).app n e.left.val)

lemma label_map (b : B) (n : SimplexCategoryᵒᵖ)
    {e e' : CostructuredArrow (elementProjection p F n) b} (f : e ⟶ e') :
    label p F a b n e' = label p F a b n e := by
  have ha := congrArg (fun k : F.obj e.left.obj ⟶ G.obj (p.obj e'.left.obj) =>
    k.app n e.left.val) (a.naturality f.left.hom)
  change (a.app e'.left.obj).app n ((F.map f.left.hom).app n e.left.val) =
    (G.map (p.map f.left.hom)).app n ((a.app e.left.obj).app n e.left.val) at ha
  have hf : (F.map f.left.hom).app n e.left.val = e'.left.val := f.left.map_val
  rw [hf] at ha
  change (G.map e'.hom).app n _ = (G.map e.hom).app n _
  rw [ha]
  have hw : p.map f.left.hom ≫ e'.hom = e.hom := CostructuredArrow.w f
  exact congrArg (fun k : G.obj (p.obj e.left.obj) ⟶ G.obj b =>
    k.app n ((a.app e.left.obj).app n e.left.val))
      ((G.map_comp _ _).symm.trans (congrArg G.map hw))

lemma label_operator (b : B) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (e : CostructuredArrow (elementProjection p F n) b) :
    label p F a b m (((commaLevels p F).map θ).app b |>.toFunctor.obj e) =
      (G.obj b).map θ (label p F a b n e) := by
  change (G.map e.hom).app m
    ((a.app e.left.obj).app m ((F.obj e.left.obj).map θ e.left.val)) = _
  have ha := congrArg (fun k => k e.left.val) ((a.app e.left.obj).naturality θ)
  exact (congrArg (fun x => (G.map e.hom).app m x) ha).trans
    (congrArg (fun k => k ((a.app e.left.obj).app n e.left.val))
      ((G.map e.hom).naturality θ))

lemma label_base {b c : B} (f : b ⟶ c) (n : SimplexCategoryᵒᵖ)
    (e : CostructuredArrow (elementProjection p F n) b) :
    label p F a c n ((CostructuredArrow.map f).obj e) =
      (G.map f).app n (label p F a b n e) :=
  congrArg (fun k : G.obj (p.obj e.left.obj) ⟶ G.obj c =>
    k.app n ((a.app e.left.obj).app n e.left.val)) (G.map_comp e.hom f)

/-- No homotopy equivalence assertion is required to define this augmentation. -/
def relativeAugmentationComponent (b : B) :
    (relative p F).obj b ⟶ SSet.uliftFunctor.{max uD vD vB, v}.obj (G.obj b) where
  app n := ↾fun c => ULift.up (label p F a b n (c.obj 0))
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    apply ULift.ext
    exact (label_operator p F a b θ (c.obj (θ.unop.toOrderHom 0))).trans
      (congrArg (fun z => (G.obj b).map θ z)
        (label_map p F a b n (c.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0))))))

/-- The augmentation is natural on all actual base morphisms. -/
def relativeAugmentation : relative p F ⟶ G ⋙ SSet.uliftFunctor.{max uD vD vB, v} where
  app b := relativeAugmentationComponent p F a b
  naturality {b c} f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (label_base p F a f n (x.obj 0))

end SerrePositivity.SimplicialModel.BarConstruction
