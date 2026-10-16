module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Nerve homotopies with independent object and Hom universes

Both nerves are explicitly lifted to a common value universe. The maps
and interval retain their actual chains, including their original arrows.
-/

@[expose] public section
universe uC vC uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.NerveHomotopyUniverse
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

def map (F : C ⥤ D) : SSet.uliftFunctor.{max uD vD, max uC vC}.obj (nerve C) ⟶
    SSet.uliftFunctor.{max uC vC, max uD vD}.obj (nerve D) where
  app _ := ↾fun c => ULift.up (c.down ⋙ F)
  naturality {_ _} _ := rfl

variable {F G : C ⥤ D} (α : F ⟶ G)

abbrev interval : Fin 2 × C ⥤ D := Functor.uncurry.obj (ComposableArrows.mk₁ α)

def hom : SSet.uliftFunctor.{max uD vD, max uC vC}.obj (nerve C) ⊗
    SSet.stdSimplex.{max uC vC uD vD}.obj (SimplexCategory.mk 1) ⟶
      SSet.uliftFunctor.{max uC vC, max uD vD}.obj (nerve D) where
  app _ := ↾fun p => ULift.up
    (((SSet.stdSimplex.objEquiv p.2).toOrderHom.monotone.functor.prod' p.1.down) ⋙ interval α)
  naturality {_ _} _ := rfl

lemma at_zero : SSet.ι₀ ≫ hom α = map F := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  apply ULift.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  change 𝟙 _ ≫ F.map (c.down.map h) =
    eqToHom rfl ≫ F.map (c.down.map h) ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

lemma at_one : SSet.ι₁ ≫ hom α = map G := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  apply ULift.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  change 𝟙 _ ≫ G.map (c.down.map h) =
    eqToHom rfl ≫ G.map (c.down.map h) ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

def homotopy : SSet.Homotopy (map F) (map G) where
  h := hom α
  h₀ := at_zero α
  h₁ := at_one α
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

end SerrePositivity.NerveHomotopyUniverse
