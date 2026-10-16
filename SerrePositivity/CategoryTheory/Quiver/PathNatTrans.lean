module

public import Mathlib.CategoryTheory.PathCategory.Basic

/-! # Natural transformations on a path category from the generator equations -/

@[expose] public section
universe u v uD vD
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.QuiverPaths
variable {V : Type u} [Quiver.{v} V] {D : Type uD} [Category.{vD} D]

def natTransOfEdges (F G : Paths V ⥤ D) (a : ∀ X, F.obj X ⟶ G.obj X)
    (ha : ∀ {X Y : V} (e : X ⟶ Y),
      F.map ((Paths.of V).map e) ≫ a Y = a X ≫ G.map ((Paths.of V).map e)) : F ⟶ G where
  app := a
  naturality {X Y} p := by
    induction p with
    | nil =>
      change F.map (𝟙 X) ≫ a X = a X ≫ G.map (𝟙 X)
      rw [F.map_id, G.map_id, Category.id_comp, Category.comp_id]
    | cons p e ih =>
      change F.map (p ≫ (Paths.of V).map e) ≫ a _ =
        a X ≫ G.map (p ≫ (Paths.of V).map e)
      rw [F.map_comp, G.map_comp, Category.assoc]
      calc
        _ = F.map p ≫ (a _ ≫ G.map ((Paths.of V).map e)) :=
          congrArg (fun k => F.map p ≫ k) (ha e)
        _ = (F.map p ≫ a _) ≫ G.map ((Paths.of V).map e) := (Category.assoc _ _ _).symm
        _ = (a X ≫ G.map p) ≫ G.map ((Paths.of V).map e) :=
          congrArg (fun k => k ≫ G.map ((Paths.of V).map e)) ih
        _ = _ := Category.assoc _ _ _

end SerrePositivity.QuiverPaths
