module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveFillerExtension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveParameterExtension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterMapping
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterRelativeChoice

/-! # Coherent whole large-parameter families with small original value spaces

Auxiliary mapping spaces can be large. Only boundary fillers of the
original small values are inputs; no large model structure is assumed.
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveLargeParameter
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})
  (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d))

abbrev lifted : D ⥤ SSet.{max w v} := F ⋙ SSet.uliftFunctor.{w, v}
abbrev mapping (K : SSet.{max w v}) := NerveParameterExtension.cotensor (lifted.{w} F) K
abbrev System (K : SSet.{max w v}) := NerveParameterExtension.System (lifted.{w} F) K

/-- Restrict a whole coherent family along any actual parameter map. -/
def restrict {A K : SSet.{max w v}} (a : System F K) (i : A ⟶ K) : System F A :=
  a ≫ NerveMonomorphismLifting.valueMap (mapping F K) (mapping F A)
    (NerveParameterExtension.restriction (lifted F) i)

lemma restrict_evaluate {A K : SSet.{max w v}} (a : System F K) (i : A ⟶ K) (d : D) :
    NerveParameterExtension.evaluate (lifted F) (restrict F a i) d =
      i ≫ NerveParameterExtension.evaluate (lifted F) a d := by
  apply NerveParameterExtension.name_injective
  rw [← RelativeChoiceSpace.name_precomp, NerveParameterExtension.name_evaluate,
    NerveParameterExtension.name_evaluate]
  rfl

lemma restrict_comp {A B K : SSet.{max w v}} (a : System F K) (i : A ⟶ B) (j : B ⟶ K) :
    restrict F (restrict F a j) i = restrict F a (i ≫ j) := by
  unfold restrict
  rw [Category.assoc]
  congr 1

variable (K : SSet.{max w v})

include hp in
lemma mappingFillers : ∀ d, UniverseLift.BoundaryFillers ((mapping F K).obj d) :=
  fun d => LargeParameterMapping.fillers (hp d) K

/-- Retain each original whole K-family while making all external chains coherent. -/
def extendFamilies (families : ∀ d, K ⟶ UniverseLift.obj.{w} (F.obj d)) : System F K :=
  NerveFillerExtension.extendVertices (mapping F K) (mappingFillers F hp K)
    (fun d => RelativeChoiceSpace.name (families d))

lemma extendFamilies_evaluate (families : ∀ d, K ⟶ UniverseLift.obj.{w} (F.obj d)) (d : D) :
    NerveParameterExtension.evaluate (lifted F) (extendFamilies F hp K families) d =
      families d := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (extendFamilies F hp K families).app (ofChain (ComposableArrows.mk₀ d))) = families d
  rw [show (extendFamilies F hp K families).app (ofChain (ComposableArrows.mk₀ d)) =
      RelativeChoiceSpace.name (families d) from
    NerveFillerExtension.extendVertices_point _ _ _ d]
  simp only [RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry']

variable {A : SSet.{max w v}} (i : A ⟶ K) [Mono i]

include hp in
lemma restriction_rightLifting : ∀ d, (MorphismProperty.monomorphisms SSet.{max w v}).rlp
    ((NerveParameterExtension.restriction (lifted F) i).app d) := by
  intro d U V l hl
  have : Mono l := hl
  exact LargeParameterRelativeChoice.restriction_lifting (hp d) i l

variable (boundary : System F A) (n : ℕ)
  (old : NerveLowerExtension.LowerSystem (mapping F K) n)
  (hboundary : old ≫ Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveMonomorphismLifting.valueMap (mapping F K) (mapping F A)
      (NerveParameterExtension.restriction (lifted F) i)) =
        Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) boundary)

/-- Relative extension retaining the whole coherent large boundary in every external degree. -/
def relative : System F K :=
  NerveMonomorphismLifting.extend (mapping F K) (mapping F A)
    (NerveParameterExtension.restriction (lifted F) i) boundary n old hboundary
    (restriction_rightLifting F hp K i)

lemma relative_boundary : relative F hp K i boundary n old hboundary ≫
    NerveMonomorphismLifting.valueMap (mapping F K) (mapping F A)
      (NerveParameterExtension.restriction (lifted F) i) = boundary :=
  NerveMonomorphismLifting.extend_boundary _ _ _ _ _ _ _ _

lemma relative_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (relative F hp K i boundary n old hboundary) = old :=
  NerveMonomorphismLifting.extend_restrict _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveLargeParameter
