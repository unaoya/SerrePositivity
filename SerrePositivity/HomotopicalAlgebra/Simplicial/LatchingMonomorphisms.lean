module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LatchingDegeneracies
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-! # Simplicial latching comparisons are monomorphisms

The latching cocone embeds its colimit into the set of simplices. Equality
of two images is witnessed by an actual common degeneracy refinement, not
by a presumed splitting of a simplicial object in an arbitrary category.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialLatching

lemma comparison_mono (X : SSet.{v}) (j : SimplexCategoryᵒᵖ) :
    Mono ((latchingComparison simplexOp j).app X) := by
  apply (mono_iff_injective _).mpr
  intro x y h
  obtain ⟨a, xa, rfl⟩ := Types.jointly_surjective' x
  obtain ⟨b, yb, rfl⟩ := Types.jointly_surjective' y
  have ha (i : LatchingIndex simplexOp j) (z : X.obj i.obj.left) :
      (latchingComparison simplexOp j).app X (colimit.ι (latchingSource simplexOp j ⋙ X) i z) =
        X.map i.obj.hom z :=
    congrArg (fun k => k z) (colimit.ι_desc (latchingCocone simplexOp X j) i)
  have h' := (ha a xa).symm.trans (h.trans (ha b yb))
  obtain ⟨r, u, w, z, hzx, hzy⟩ := common_refinement X a b xa yb h'
  have hu := congrArg (fun k => k z) (colimit.w (latchingSource simplexOp j ⋙ X) u)
  have hw := congrArg (fun k => k z) (colimit.w (latchingSource simplexOp j ⋙ X) w)
  change colimit.ι (latchingSource simplexOp j ⋙ X) a (X.map u.hom.left z) =
    colimit.ι (latchingSource simplexOp j ⋙ X) r z at hu
  change colimit.ι (latchingSource simplexOp j ⋙ X) b (X.map w.hom.left z) =
    colimit.ι (latchingSource simplexOp j ⋙ X) r z at hw
  rw [hzx] at hu
  rw [hzy] at hw
  exact hu.trans hw.symm

end SerrePositivity.SimplicialLatching
