module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation

/-! # Whole family compatibility derived from actual objectwise boundary equations -/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveMovingFamilyFit
variable {D : Type uD} [Category.{vD} D]
  (K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v})

/-- Every coherent boundary recovers its entire degree-zero system from its actual evaluations. -/
lemma lower_recover (a : NerveMovingParameter.System K F) :
    NerveMovingParameter.vertices K F (NerveMovingParameter.evaluate K F a) =
      Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1) a := by
  apply NatTrans.ext
  funext s
  rcases s with ⟨s, hs⟩
  rcases s with @⟨m, c⟩
  rcases m with ⟨⟨n⟩⟩
  change n < 1 at hs
  have hn : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hs)
  subst n
  change ComposableArrows D 0 at c
  obtain ⟨d, rfl⟩ := ComposableArrows.mk₀_surjective c
  exact (NerveMovingParameter.vertices_at_object K F _ d).trans
    (NerveBiparameterMaps.name_evaluate K F a d)

variable (L : D ⥤ SSet.{max w v}) (i : L ⟶ K)
  (families : ∀ d, K.obj d ⟶ UniverseLift.obj.{w} (F.obj d))

lemma vertices_restriction : NerveMovingParameter.vertices K F families ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveMovingParameterRelative.restriction L K i F) =
    NerveMovingParameter.vertices L F (fun d => i.app d ≫ families d) := by
  apply NatTrans.ext
  funext s
  rcases s with ⟨s, hs⟩
  rcases s with @⟨m, c⟩
  rcases m with ⟨⟨n⟩⟩
  change n < 1 at hs
  have hn : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hs)
  subst n
  change ComposableArrows D 0 at c
  obtain ⟨d, rfl⟩ := ComposableArrows.mk₀_surjective c
  change (NerveMovingParameter.vertices K F families).app
    ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_one⟩ ≫
      (NerveMovingParameterRelative.restriction L K i F).app
        (ofChain (ComposableArrows.mk₀ d)) = _
  rw [NerveMovingParameter.vertices_at_object, NerveMovingParameter.vertices_at_object,
    NerveMovingParameterRelative.restriction_app]
  exact RelativeChoiceSpace.name_precomp (i.app d) (families d)

variable (target : NerveMovingParameter.System L F)
  (he : ∀ d, i.app d ≫ families d = NerveMovingParameter.evaluate L F target d)

include he in
lemma compatible : NerveMovingParameter.vertices K F families ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveMovingParameterRelative.restriction L K i F) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1) target := by
  rw [vertices_restriction, funext he, lower_recover]

variable (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d)) (hi : ∀ d, Mono (i.app d))

/-- Objectwise equations supply the lower-system fit, with no extra coherent fit input. -/
def extend : NerveMovingParameter.System K F :=
  NerveMovingParameterRelative.extendFamilies L K i F hp hi target families
    (compatible K F L i families target he)

lemma extend_evaluate (d : D) : NerveMovingParameter.evaluate K F
    (extend K F L i families target he hp hi) d = families d :=
  NerveMovingParameterRelative.extendFamilies_evaluate _ _ _ _ _ _ _ _ _ d

lemma extend_boundary : extend K F L i families target he hp hi ≫
    NerveMovingParameterRelative.restriction L K i F = target :=
  NerveMovingParameterRelative.extendFamilies_boundary _ _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveMovingFamilyFit
