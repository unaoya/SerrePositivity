module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryFillerLifting

/-! # Whole coherent systems from objectwise boundary fillers, with no model structure -/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveFillerExtension
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})
  (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d))
  (n : ℕ) (old : NerveLowerExtension.LowerSystem F n)

abbrev point : D ⥤ SSet.{v} := (Functor.const D).obj
  (SSet.stdSimplex.obj (SimplexCategory.mk 0))

lemma boundary : old ≫ Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveMonomorphismLifting.valueMap F (point (D := D))
      (NerveCoherentExtension.projection F)) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (NerveCoherentFamily.collapse (D := D)) := by
  apply NatTrans.ext
  funext s
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

include hp in
lemma rightLifting : ∀ d, (MorphismProperty.monomorphisms SSet.{v}).rlp
    ((NerveCoherentExtension.projection F).app d) :=
  fun d => BoundaryFillerLifting.terminal_rightLifting (hp d)

def extend : NerveCoherentFamily.System F :=
  NerveMonomorphismLifting.extend F (point (D := D)) (NerveCoherentExtension.projection F)
    (NerveCoherentFamily.collapse (D := D)) n old (boundary F n old) (rightLifting F hp)

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend F hp n old) = old :=
  NerveMonomorphismLifting.extend_restrict _ _ _ _ _ _ _ _

lemma extend_component (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend F hp n old).app s.obj = old.app s := congr_app (extend_restrict F hp n old) s

/-- Retain arbitrary independent points in values with boundary fillers. -/
def extendVertices (points : ∀ d, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj d) :
    NerveCoherentFamily.System F := extend F hp 1 (NerveLowerExtension.vertices F points)

lemma extendVertices_point
    (points : ∀ d, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj d) (d : D) :
    (extendVertices F hp points).app (ofChain (ComposableArrows.mk₀ d)) = points d :=
  (extend_component F hp 1 (NerveLowerExtension.vertices F points)
    ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_one⟩).trans
      (NerveLowerExtension.vertices_component F points d)

end SerrePositivity.SimplicialModel.NerveFillerExtension
