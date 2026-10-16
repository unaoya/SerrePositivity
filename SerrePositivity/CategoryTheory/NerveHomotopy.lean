module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Actual simplicial homotopies induced by natural transformations

The interval diagram of functors is uncurried and evaluated on each
simplex and its monotone interval parameter. All dimensions use one formula.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.NerveHomotopy
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G : C ⥤ D} (α : F ⟶ G)

abbrev interval : Fin 2 × C ⥤ D := Functor.uncurry.obj (ComposableArrows.mk₁ α)

def hom : nerve C ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶ nerve D where
  app _n := ↾fun p => ((SSet.stdSimplex.objEquiv p.2).toOrderHom.monotone.functor.prod' p.1) ⋙
    interval α
  naturality {_ _} _ := rfl

@[reassoc]
lemma at_zero : SSet.ι₀ ≫ hom α = nerveMap F := by
  apply NatTrans.ext
  funext n
  refine ConcreteCategory.hom_ext _ _ (fun E => ?_)
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  change 𝟙 _ ≫ F.map (E.map h) = eqToHom rfl ≫ F.map (E.map h) ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

@[reassoc]
lemma at_one : SSet.ι₁ ≫ hom α = nerveMap G := by
  apply NatTrans.ext
  funext n
  refine ConcreteCategory.hom_ext _ _ (fun E => ?_)
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  change 𝟙 _ ≫ G.map (E.map h) = eqToHom rfl ≫ G.map (E.map h) ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

def homotopy : SSet.Homotopy (nerveMap F) (nerveMap G) where
  h := hom α
  h₀ := at_zero α
  h₁ := at_one α
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property


abbrev point (a : C) : SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0) ⟶ nerve C :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₀ a)

lemma constant_eq (a : C) :
    SSet.stdSimplex.isTerminalObj₀.from (nerve C) ≫ point a =
      nerveMap ((Functor.const C).obj a) := by
  apply NatTrans.ext
  funext n
  refine ConcreteCategory.hom_ext _ _ (fun E => ?_)
  rfl

end SerrePositivity.NerveHomotopy
