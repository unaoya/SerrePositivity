module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Setoid.Basic

/-! # Quotients of entire simplicial diagrams by stable degreewise congruences

Both base action and simplicial operators descend through the same relation.
The base may be large. No homotopical assertion about the quotient is assumed.
-/

@[expose] public section
universe w uD vD
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.DiagramQuotient
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{w})

structure Congruence where
  rel : ∀ d n, Setoid ((F.obj d).obj n)
  simplicial : ∀ d {n m} (θ : n ⟶ m) {x y},
    (rel d n).r x y → (rel d m).r ((F.obj d).map θ x) ((F.obj d).map θ y)
  base : ∀ {d e} (f : d ⟶ e) n {x y},
    (rel d n).r x y → (rel e n).r ((F.map f).app n x) ((F.map f).app n y)

/-- Erasing all degreewise labels is stable, but need not preserve homotopy types. -/
def total : Congruence F where
  rel _ _ := ⊤
  simplicial _ {_ _} _ {_ _} _ := trivial
  base {_ _} _ _ {_ _} _ := trivial

variable {F} (R : Congruence F)

def value (d : D) : SSet.{w} where
  obj n := Quotient (R.rel d n)
  map θ := ↾(Quotient.map ((F.obj d).map θ) (fun _ _ h => R.simplicial d θ h))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact congrArg (Quotient.mk (R.rel d n)) (types_congr_hom ((F.obj d).map_id n) x)
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact congrArg (Quotient.mk _)
      (types_congr_hom ((F.obj d).map_comp θ φ) x)

def action {d e : D} (f : d ⟶ e) : value R d ⟶ value R e where
  app n := ↾(Quotient.map ((F.map f).app n) (fun _ _ h => R.base f n h))
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact congrArg (Quotient.mk _) (types_congr_hom ((F.map f).naturality θ) x)

def functor : D ⥤ SSet.{w} where
  obj := value R
  map := action R
  map_id d := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact congrArg (Quotient.mk _)
      (types_congr_hom (congr_app (F.map_id d) n) x)
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact congrArg (Quotient.mk _)
      (types_congr_hom (congr_app (F.map_comp f g) n) x)

def projection : F ⟶ functor R where
  app _ :=
    { app _ := ↾(Quotient.mk _)
      naturality {_ _} _ := rfl }
  naturality {_ _} _ := rfl

lemma projection_surjective (d : D) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (((projection R).app d).app n) := Quotient.mk_surjective

instance total_subsingleton (d : D) (n : SimplexCategoryᵒᵖ) :
    Subsingleton ((value (total F) d).obj n) := by
  constructor
  intro a b
  refine Quotient.inductionOn a (fun x => ?_)
  refine Quotient.inductionOn b (fun y => ?_)
  exact Quotient.sound trivial

end SerrePositivity.SimplicialModel.DiagramQuotient
