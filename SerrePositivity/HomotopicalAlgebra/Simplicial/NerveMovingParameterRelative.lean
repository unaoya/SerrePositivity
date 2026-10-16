module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMovingParameter

/-! # Retaining coherent moving boundaries in changing parameter diagrams -/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveMovingParameterRelative
variable {D : Type uD} [Category.{vD} D]
  (L K : D ⥤ SSet.{max w v}) (i : L ⟶ K) (F : D ⥤ SSet.{v})

def restriction : NerveMovingParameter.values K F ⟶ NerveMovingParameter.values L F :=
  Functor.whiskerLeft (NerveBiparameter.endpoints D)
    (Functor.whiskerRight (NatTrans.prod (NatTrans.op i) (𝟙 (NerveMovingParameter.lifted.{w} F)))
      (Functor.uncurry.obj MonoidalClosed.internalHom))

lemma restriction_app (s : Index D) : (restriction L K i F).app s =
    (pre (i.app (NerveSimplexStart.start s))).app (UniverseLift.obj.{w} (F.obj (endpoint s))) := by
  change (pre (i.app (NerveSimplexStart.start s))).app
      (UniverseLift.obj.{w} (F.obj (endpoint s))) ≫
    (ihom (L.obj (NerveSimplexStart.start s))).map
      (𝟙 (UniverseLift.obj.{w} (F.obj (endpoint s)))) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

variable (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d))
  (hi : ∀ d, Mono (i.app d))

include hp hi in
lemma rightLifting : ∀ s, (MorphismProperty.monomorphisms SSet.{max w v}).rlp
    ((restriction L K i F).app s) := by
  intro s A B j hj
  have : Mono j := hj
  have : Mono (i.app (NerveSimplexStart.start s)) := hi _
  rw [restriction_app]
  exact LargeParameterRelativeChoice.restriction_lifting (hp (endpoint s)) _ j

variable (target : NerveMovingParameter.System L F) (n : ℕ)
  (old : NerveMovingParameter.LowerSystem K F n)
  (hboundary : old ≫ Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (restriction L K i F) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) target)

/-- Keep the entire moving boundary system and the entire prescribed lower parameter system. -/
def extend : NerveMovingParameter.System K F :=
  NerveDiagramExtension.extend (NerveMovingParameter.values K F) (NerveMovingParameter.values L F)
    (restriction L K i F) (NerveMovingParameter.values_inverts K F)
    (NerveMovingParameter.values_inverts L F) (rightLifting L K i F hp hi)
    target n old hboundary

lemma extend_boundary : extend L K i F hp hi target n old hboundary ≫ restriction L K i F =
    target := NerveDiagramExtension.extend_boundary _ _ _ _ _ _ _ _ _ _

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend L K i F hp hi target n old hboundary) = old :=
  NerveDiagramExtension.extend_restrict _ _ _ _ _ _ _ _ _ _

lemma extend_component (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend L K i F hp hi target n old hboundary).app s.obj = old.app s :=
  congr_app (extend_restrict L K i F hp hi target n old hboundary) s

variable (families : ∀ d, K.obj d ⟶ UniverseLift.obj.{w} (F.obj d))
  (hfamilies : NerveMovingParameter.vertices K F families ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1) (restriction L K i F) =
      Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1) target)

def extendFamilies : NerveMovingParameter.System K F :=
  extend L K i F hp hi target 1 (NerveMovingParameter.vertices K F families) hfamilies

lemma extendFamilies_evaluate (d : D) :
    NerveMovingParameter.evaluate K F (extendFamilies L K i F hp hi target families hfamilies) d =
      families d := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (extendFamilies L K i F hp hi target families hfamilies).app
      (ofChain (ComposableArrows.mk₀ d))) = families d
  rw [show (extendFamilies L K i F hp hi target families hfamilies).app
      (ofChain (ComposableArrows.mk₀ d)) = RelativeChoiceSpace.name (families d) from
    (extend_component L K i F hp hi target 1 (NerveMovingParameter.vertices K F families) hfamilies
      ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_one⟩).trans
        (NerveMovingParameter.vertices_at_object K F families d)]
  simp only [RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry']

lemma extendFamilies_boundary : extendFamilies L K i F hp hi target families hfamilies ≫
    restriction L K i F = target := extend_boundary _ _ _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveMovingParameterRelative
