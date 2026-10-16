module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexMonomorphismLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveLowerExtension

/-! # Relative coherent lifting without a model structure in the value universe

Objectwise right lifting against monomorphisms supplies the local Reedy
lifts. The whole target system and the specified lower lift stay fixed.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.NerveSimplexEndpoint
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveMonomorphismLifting
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

variable (hp : ∀ d, (MorphismProperty.monomorphisms SSet.{v}).rlp (p.app d))

include hp in
lemma reedyRight : Reedy.reedyRight (NerveCoherentFamily.reedy D)
    ((MorphismProperty.monomorphisms SSet.{v}).rlp) (valueMap F G p) :=
  SimplexMonomorphismLifting.reedyRight (nerve D) (NerveCoherentFamily.values F)
    (NerveCoherentFamily.values G) (valueMap F G p)
    (fun f hf => by
      have := NerveCoherentFamily.endpointMap_isIso f hf
      exact Functor.map_isIso (F := F) _)
    (fun f hf => by
      have := NerveCoherentFamily.endpointMap_isIso f hf
      exact Functor.map_isIso (F := G) _)
    (fun s => hp (endpoint s))

/-- The initial relative latching arrow is mono, without a value-side model. -/
lemma parameter_mono (s : Index D) : Mono
    (relativeLatchingMap (NerveCoherentFamily.reedy D) s
      (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D))) := by
  have : IsIso ((latchingComparison (NerveCoherentFamily.reedy D) s).app
      (⊥_ (Index D ⥤ SSet.{v}))) :=
    isIso_of_isInitial
      (initialIsInitial.isInitialObj (latchingEvaluation (NerveCoherentFamily.reedy D) s)
        (⊥_ (Index D ⥤ SSet.{v})))
      (initialIsInitial.isInitialObj ((evaluation (Index D) SSet.{v}).obj s)
        (⊥_ (Index D ⥤ SSet.{v}))) _
  let hi : Arrow.mk ((latchingComparison (NerveCoherentFamily.reedy D) s).app
      (NerveCoherentFamily.simplices.{vD, uD, v} D)) ≅
      Arrow.mk (relativeLatchingMap (NerveCoherentFamily.reedy D) s
        (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D))) :=
    Arrow.isoMk (asIso (pushout.inl
      ((latchingEvaluation (NerveCoherentFamily.reedy D) s).map
        (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D)))
      ((latchingComparison (NerveCoherentFamily.reedy D) s).app
        (⊥_ (Index D ⥤ SSet.{v}))))) (Iso.refl _)
      ((inl_relativeLatchingMap (NerveCoherentFamily.reedy D) s
        (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D))).trans (Category.comp_id _).symm)
  exact ((MorphismProperty.monomorphisms SSet.{v}).arrow_iso_iff hi).mp
    (SimplexLatchingBoundary.latching_mono (nerve D) s)

include hp in
lemma localLifting : ∀ s, HasLiftingProperty
    (relativeLatchingMap (NerveCoherentFamily.reedy D) s
      (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D)))
    (relativeMatchingMap (NerveCoherentFamily.reedy D) s (valueMap F G p)) :=
  fun s => (reedyRight F G p hp s) _ (parameter_mono (D := D) s)

/-- Lift the whole target system while retaining every specified old component. -/
def extend : NerveCoherentFamily.System F := by
  let := localLifting F G p hp
  exact RelativeLifting.lift (NerveCoherentFamily.reedy D) (square F G p target) n
    (below F G p target n old hboundary)

lemma extend_boundary : extend F G p target n old hboundary hp ≫ valueMap F G p = target := by
  let := localLifting F G p hp
  exact RelativeLifting.fac_right (NerveCoherentFamily.reedy D) (square F G p target) n
    (below F G p target n old hboundary)

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend F G p target n old hboundary hp) = old := by
  let := localLifting F G p hp
  exact RelativeLifting.restrict (NerveCoherentFamily.reedy D) (square F G p target) n
    (below F G p target n old hboundary)

lemma extend_component (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend F G p target n old hboundary hp).app s.obj = old.app s :=
  congr_app (extend_restrict F G p target n old hboundary hp) s

end SerrePositivity.SimplicialModel.NerveMonomorphismLifting
