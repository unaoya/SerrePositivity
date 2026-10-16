module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveCoherentFamily

/-! # Reindexing whole coherent systems along actual functors of center categories -/

@[expose] public section
universe v u vE uE w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveCoherentReindex
variable {D : Type u} [Category.{v} D] {E : Type uE} [Category.{vE} E] (H : E ⥤ D)

def index : Index E ⥤ Index D where
  obj s := Opposite.op ((nerve D).elementsMk s.unop.obj (s.unop.val ⋙ H))
  map {s t} f := Quiver.Hom.op (Functor.Elements.homMk f.unop.hom (by
    change (SimplexCategory.toCat.map (operator f)).toFunctor ⋙ (chain t ⋙ H) = chain s ⋙ H
    rw [← Functor.assoc, chain_eq f]))
  map_id _ := rfl
  map_comp _ _ := rfl

lemma operator_map {s t : Index E} (f : s ⟶ t) : operator ((index H).map f) = operator f := rfl

lemma endpoint_obj (s : Index E) : endpoint ((index H).obj s) = H.obj (endpoint s) := rfl

lemma endpoint_map {s t : Index E} (f : s ⟶ t) :
    endpointMap ((index H).map f) = H.map (endpointMap f) := by
  dsimp only [endpointMap, tail]
  rw [H.map_comp, eqToHom_map]
  rfl

variable (F : D ⥤ SSet.{w}) (a : NerveCoherentFamily.System F)

/-- Retain every component of the original coherent system on the reindexed chain. -/
def reindex : NerveCoherentFamily.System (H ⋙ F) where
  app s := a.app ((index H).obj s)
  naturality {s t} f := by
    have h := a.naturality ((index H).map f)
    change SSet.stdSimplex.map (operator f) ≫ a.app ((index H).obj t) =
      a.app ((index H).obj s) ≫ F.map (H.map (endpointMap f))
    rw [← endpoint_map H f]
    exact h

lemma reindex_component (s : Index E) : (reindex H F a).app s = a.app ((index H).obj s) := rfl

end SerrePositivity.SimplicialModel.NerveCoherentReindex
