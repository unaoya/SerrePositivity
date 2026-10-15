module

public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-! # Partial coherent lifts along an ordered diagram

The inverse system records actual compatible lifts through a natural
transformation. Its transition maps restrict to smaller initial segments.
No model structure is used.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel.ContinuousLifts
variable {J : Type w} [LinearOrder J] {C : Type u} [Category.{v} C]
  {D U V : J ⥤ C} (p : U ⟶ V) (b : D ⟶ V)

@[ext]
structure Partial (j : J) where
  hom (i : J) (hi : i ≤ j) : D.obj i ⟶ U.obj i
  naturality {i k : J} (hik : i ≤ k) (hk : k ≤ j) :
    D.map (homOfLE hik) ≫ hom k hk = hom i (hik.trans hk) ≫ U.map (homOfLE hik)
  fac (i : J) (hi : i ≤ j) : hom i hi ≫ p.app i = b.app i

namespace Partial
variable {p b} {j k : J} (x : Partial p b j)

def restrict (h : k ≤ j) : Partial p b k where
  hom i hi := x.hom i (hi.trans h)
  naturality hik hk := x.naturality hik (hk.trans h)
  fac i hi := x.fac i (hi.trans h)

@[simp]
lemma restrict_hom (h : k ≤ j) (i : J) (hi : i ≤ k) :
    (x.restrict h).hom i hi = x.hom i (hi.trans h) := rfl

end Partial

def system : Jᵒᵖ ⥤ Type (max w v) where
  obj j := Partial p b j.unop
  map f := ↾fun x => x.restrict (leOfHom f.unop)
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Partial.ext
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Partial.ext
    rfl

end SerrePositivity.DiagramModel.ContinuousLifts
