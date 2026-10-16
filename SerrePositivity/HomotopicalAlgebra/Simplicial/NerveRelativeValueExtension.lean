module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNaturalMatching
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveLowerExtension

/-! # Relative coherent lifting over a prescribed whole value system

A pointwise trivial fibration of value diagrams gives a coherent lifting
problem. A specified lower-degree lift is retained exactly, and the entire
already coherent target system is retained in every degree.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.NerveSimplexEndpoint
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveRelativeValueExtension
variable {D : Type uD} [Category.{vD} D] (F G : D ⥤ SSet.{v}) (p : F ⟶ G)

abbrev valueMap : NerveCoherentFamily.values F ⟶ NerveCoherentFamily.values G :=
  Functor.whiskerLeft (NerveSimplexEndpoint.functor D) p

lemma square (target : NerveCoherentFamily.System G) :
    CommSq (initial.to (NerveCoherentFamily.values F))
      (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D)) (valueMap F G p) target :=
  ⟨initialIsInitial.hom_ext _ _⟩

variable (target : NerveCoherentFamily.System G) (n : ℕ)
  (old : NerveLowerExtension.LowerSystem F n)
  (hboundary : old ≫ Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (valueMap F G p) = Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) target)

def below : LiftBelow (NerveCoherentFamily.reedy D) (square F G p target) n where
  hom := old
  fac_left := by
    apply NatTrans.ext
    funext s
    exact (initialIsInitial.isInitialObj
      ((evaluation (Index D) SSet.{v}).obj s.obj) (⊥_ (Index D ⥤ SSet.{v}))).hom_ext _ _
  fac_right := hboundary

variable [ModelCategory SSet.{v}] (hp : ∀ d, trivialFibrations SSet.{v} (p.app d))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hp in
lemma reedyRight : Reedy.reedyRight (NerveCoherentFamily.reedy D)
    (trivialFibrations SSet.{v}) (valueMap F G p) :=
  SimplexNaturalMatching.reedyRight (nerve D) (NerveCoherentFamily.values F)
    (NerveCoherentFamily.values G) (valueMap F G p)
    (fun f hf => by
      have := NerveCoherentFamily.endpointMap_isIso f hf
      exact Functor.map_isIso (F := F) _)
    (fun f hf => by
      have := NerveCoherentFamily.endpointMap_isIso f hf
      exact Functor.map_isIso (F := G) _)
    (fun s => hp (endpoint s))

include hp hcof in
lemma localLifting : ∀ s, HasLiftingProperty
    (relativeLatchingMap (NerveCoherentFamily.reedy D) s
      (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D)))
    (relativeMatchingMap (NerveCoherentFamily.reedy D) s (valueMap F G p)) :=
  fun s => MorphismProperty.hasLiftingProperty_of_wfs _ _
    (NerveCoherentExtension.parameterCofibrant (D := D) hcof s) (reedyRight F G p hp s)

/-- Lift the whole target system while retaining every specified old component. -/
def extend : NerveCoherentFamily.System F := by
  let := localLifting F G p hp hcof
  exact RelativeLifting.lift (NerveCoherentFamily.reedy D) (square F G p target) n
    (below F G p target n old hboundary)

lemma extend_boundary : extend F G p target n old hboundary hp hcof ≫ valueMap F G p = target := by
  let := localLifting F G p hp hcof
  exact RelativeLifting.fac_right (NerveCoherentFamily.reedy D) (square F G p target) n
    (below F G p target n old hboundary)

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend F G p target n old hboundary hp hcof) = old := by
  let := localLifting F G p hp hcof
  exact RelativeLifting.restrict (NerveCoherentFamily.reedy D) (square F G p target) n
    (below F G p target n old hboundary)

lemma extend_component (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend F G p target n old hboundary hp hcof).app s.obj = old.app s :=
  congr_app (extend_restrict F G p target n old hboundary hp hcof) s

end SerrePositivity.SimplicialModel.NerveRelativeValueExtension
