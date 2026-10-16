module

public import SerrePositivity.CategoryTheory.AnchoredChain
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-! # The actual simplicial set of chains with fixed external endpoints

All ordinal operators act by reindexing the internal diagram and composing
the surrounding arrows. The object and Hom universes remain independent;
the set of chains uses their maximum, as it contains internal objects.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.AnchoredChain
variable {D : Type u} [Category.{v} D] {Y V : D} (g : Y ⟶ V)

def simplicial : SSet.{max u v} where
  obj n := AnchoredChain g n.unop.len
  map θ := ↾fun c => reindex c θ.unop.toOrderHom
  map_id _ := by
    ext c
    exact reindex_id c
  map_comp θ φ := by
    ext c
    exact (reindex_comp c θ.unop.toOrderHom φ.unop.toOrderHom).symm

end SerrePositivity.AnchoredChain
