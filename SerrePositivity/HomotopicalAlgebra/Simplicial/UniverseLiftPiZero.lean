module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLift
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-! # Actual components commute with the explicit universe lift

The equivalence is defined on vertices and edges, with no model structure.
-/

@[expose] public section
universe v w
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.UniverseLiftPiZero
variable {X Y : SSet.{v}}

def up (X : SSet.{v}) : SSet.π₀ X → SSet.π₀ (SSet.uliftFunctor.{w, v}.obj X) :=
  SSet.π₀.lift (fun x => SSet.π₀.mk ⟨x⟩) (fun {_x _y} e => SSet.π₀.sound
    (SSet.Edge.ofTruncated
      { edge := ⟨e.edge⟩
        src_eq := ULift.ext e.src_eq
        tgt_eq := ULift.ext e.tgt_eq }))

def down (X : SSet.{v}) : SSet.π₀ (SSet.uliftFunctor.{w, v}.obj X) → SSet.π₀ X :=
  SSet.π₀.lift (fun x => SSet.π₀.mk x.down) (fun {_x _y} e => SSet.π₀.sound
    (SSet.Edge.ofTruncated
      { edge := e.edge.down
        src_eq := congrArg ULift.down e.src_eq
        tgt_eq := congrArg ULift.down e.tgt_eq }))

def equiv (X : SSet.{v}) : SSet.π₀ (SSet.uliftFunctor.{w, v}.obj X) ≃ SSet.π₀ X where
  toFun := down X
  invFun := up X
  left_inv z := by
    obtain ⟨⟨x⟩, rfl⟩ := SSet.π₀.mk_surjective z
    rfl
  right_inv z := by
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
    rfl

lemma up_naturality (f : X ⟶ Y) (z : SSet.π₀ X) :
    SSet.mapπ₀ (SSet.uliftFunctor.{w, v}.map f) (up X z) = up Y (SSet.mapπ₀ f z) := by
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
  rfl

lemma down_naturality (f : X ⟶ Y)
    (z : SSet.π₀ (SSet.uliftFunctor.{w, v}.obj X)) :
    down Y (SSet.mapπ₀ (SSet.uliftFunctor.{w, v}.map f) z) = SSet.mapπ₀ f (down X z) := by
  obtain ⟨⟨x⟩, rfl⟩ := SSet.π₀.mk_surjective z
  rfl

end SerrePositivity.SimplicialModel.UniverseLiftPiZero
