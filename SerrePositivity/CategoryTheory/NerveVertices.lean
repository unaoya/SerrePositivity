module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import SerrePositivity.HomotopicalAlgebra.Simplicial.VertexTuples

/-! # The actual vertex subcomplex of a category nerve -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.NerveVertices
variable (C : Type u) [Category.{v} C]

abbrev vertices : SSet.{max u v} := SimplicialModel.VertexTuples.vertices (ULift.{v} C)

def inclusion : vertices C ⟶ nerve C where
  app _ := ↾fun x => (Functor.const _).obj x.down
  naturality {_ _} _ := rfl

instance : Mono (inclusion C) := by
  have : ∀ n, Mono ((inclusion C).app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (fun x y h =>
      ULift.ext (Functor.congr_obj h 0))
  exact NatTrans.mono_of_mono_app _

@[reassoc]
lemma vertex_inclusion (a : C) :
    SimplicialModel.VertexTuples.vertex (⟨a⟩ : ULift.{v} C) ≫ inclusion C =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₀ a) := rfl

end SerrePositivity.NerveVertices
