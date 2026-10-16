module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftFillers
public import Mathlib.CategoryTheory.Elements

/-! # Explicit simplex-category equivalence for a known universe lift

Only the ULift wrapper on each original simplex is changed. All degrees
and simplex operators are preserved. This is not a shrinking construction
for an arbitrary large simplicial set.
-/

@[expose] public section
universe w v
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.UniverseLift
variable (X : SSet.{v})

def downElements : (obj.{w} X).Elements ⥤ X.Elements where
  obj e := X.elementsMk e.obj e.val.down
  map f := Functor.Elements.homMk f.hom (congrArg ULift.down f.map_val)

def upElements : X.Elements ⥤ (obj.{w} X).Elements where
  obj e := (obj.{w} X).elementsMk e.obj (ULift.up e.val)
  map f := Functor.Elements.homMk f.hom (congrArg ULift.up f.map_val)

def elementsEquivalence : X.Elements ≌ (obj.{w} X).Elements where
  functor := upElements X
  inverse := downElements X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intro _ _ _; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intro _ _ _; rfl)

lemma downElements_degree (e : (obj.{w} X).Elements) :
    ((downElements X).obj e).obj = e.obj := rfl

lemma downElements_operator {e e' : (obj.{w} X).Elements} (f : e ⟶ e') :
    ((downElements X).map f).hom = f.hom := rfl

end SerrePositivity.SimplicialModel.UniverseLift
