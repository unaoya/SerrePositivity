module

public import Mathlib.CategoryTheory.PathCategory.Basic

/-! # Functors out of a path category are determined by vertices and generating edges -/

@[expose] public section
universe u v uD vD
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.QuiverPaths
variable {V : Type u} [Quiver.{v} V] {D : Type uD} [Category.{vD} D]

lemma prefunctor_hext {F G : V ⥤q D} (ho : ∀ X, F.obj X = G.obj X)
    (hm : ∀ {X Y : V} (e : X ⟶ Y), HEq (F.map e) (G.map e)) : F = G := by
  cases F with
  | mk fo fm =>
    cases G with
    | mk go gm =>
      have he : fo = go := funext ho
      subst go
      congr 1
      funext X Y e
      exact eq_of_heq (hm e)

lemma functor_ext_edges (F G : Paths V ⥤ D) (ho : ∀ X, F.obj X = G.obj X)
    (hm : ∀ {X Y : V} (e : X ⟶ Y),
      HEq (F.map ((Paths.of V).map e)) (G.map ((Paths.of V).map e))) : F = G := by
  have he : Paths.of V ⋙q F.toPrefunctor = Paths.of V ⋙q G.toPrefunctor :=
    prefunctor_hext ho (fun e => hm e)
  exact (Paths.lift_unique _ F he).trans (Paths.lift_unique _ G rfl).symm

end SerrePositivity.QuiverPaths
