module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarUnit
public import SerrePositivity.CategoryTheory.NerveHomotopy

/-! # The identity-projection bar has an explicit pointwise augmentation section

The section is not asserted to be natural on base morphisms. The augmentation
and the bar unit, which will form the natural span, are natural.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

abbrev identityPoint (d : D) (n : SimplexCategoryᵒᵖ) (x : (F.obj d).obj n) :
    CostructuredArrow (elementProjection (𝟭 D) F n) d :=
  CostructuredArrow.mk (Y := (F.flip.obj n).elementsMk d x) (𝟙 d)

/-- Constant comma chains supply a section at each fixed base object. -/
def identitySection (d : D) : SSet.uliftFunctor.{max uD vD, v}.obj (F.obj d) ⟶
    (relative (𝟭 D) F).obj d where
  app n := ↾fun x => (Functor.const (Fin (n.unop.len + 1))).obj (identityPoint F d n x.down)
  naturality {_ _} _ := rfl

lemma identitySection_retract (d : D) :
    identitySection F d ≫ (identityAugmentation F).app d = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply ULift.ext
  change (F.map (𝟙 d)).app n x.down = x.down
  rw [F.map_id]
  rfl

/-- The degreewise collapse sends every element to its image at the comma target. -/
def identityCollapse (d : D) (n : SimplexCategoryᵒᵖ) :
    CostructuredArrow (elementProjection (𝟭 D) F n) d ⥤
      CostructuredArrow (elementProjection (𝟭 D) F n) d where
  obj e := identityPoint F d n ((F.map e.hom).app n e.left.val)
  map {e e'} f := CostructuredArrow.homMk
    (Functor.Elements.homMk (𝟙 d) (by
      change (F.map (𝟙 d)).app n _ = _
      rw [F.map_id]
      exact (label_map (𝟭 D) F (𝟙 F) d n f).symm)) (by simp)

/-- Each degreewise comma category contracts towards its identity presentations. -/
def identityContraction (d : D) (n : SimplexCategoryᵒᵖ) :
    𝟭 (CostructuredArrow (elementProjection (𝟭 D) F n) d) ⟶ identityCollapse F d n where
  app e := CostructuredArrow.homMk (Functor.Elements.homMk e.hom rfl) (by
    change e.hom ≫ 𝟙 d = e.hom
    exact Category.comp_id _)
  naturality {e e'} f := by
    apply CostructuredArrow.hom_ext
    apply Functor.Elements.hom_ext
    change f.left.hom ≫ e'.hom = e.hom ≫ 𝟙 d
    exact (CostructuredArrow.w f).trans (Category.comp_id _).symm

private lemma elements_transport {K : D ⥤ Type v} {x y : K.Elements} (h : x = y) :
    (eqToHom h).hom = eqToHom (congrArg (fun e : K.Elements => e.obj) h) := by
  cases h
  rfl

/-- The collapse of an entire chain is the actual augmentation followed by its section. -/
lemma identityCollapse_chain (d : D) (n : SimplexCategoryᵒᵖ)
    (c : ComposableArrows (CostructuredArrow (elementProjection (𝟭 D) F n) d) n.unop.len) :
    c ⋙ identityCollapse F d n =
      (Functor.const (Fin (n.unop.len + 1))).obj
        (identityPoint F d n ((F.map (c.obj 0).hom).app n (c.obj 0).left.val)) := by
  refine CategoryTheory.Functor.ext (fun i => congrArg (identityPoint F d n)
    (label_map (𝟭 D) F (𝟙 F) d n (c.map (homOfLE (Fin.zero_le i))))) ?_
  intro i j h
  apply CostructuredArrow.hom_ext
  apply Functor.Elements.hom_ext
  simp [elements_transport]
  rfl

/-- At each simplicial degree the actual nerve maps are joined by a full simplicial homotopy. -/
def identityNerveHomotopy (d : D) (n : SimplexCategoryᵒᵖ) :
    SSet.Homotopy
      (nerveMap (𝟭 (CostructuredArrow (elementProjection (𝟭 D) F n) d)))
      (nerveMap (identityCollapse F d n)) :=
  SerrePositivity.NerveHomotopy.homotopy (identityContraction F d n)

end SerrePositivity.SimplicialModel.BarConstruction
