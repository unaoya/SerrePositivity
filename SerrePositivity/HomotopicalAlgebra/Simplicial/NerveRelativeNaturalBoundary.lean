module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveNaturalBoundary

/-! # Moving relative extension with a prescribed strict natural boundary

The low-degree compatibility is derived from the actual objectwise
boundary equations. No coherent boundary or compatibility is left as an
additional input: the natural boundary supplies its whole canonical system.
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveRelativeNaturalBoundary
variable {D : Type uD} [Category.{vD} D]
  (L K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v}) (i : L ⟶ K)
  (b : L ⟶ NerveMovingParameter.lifted.{w} F)
  (families : ∀ d, K.obj d ⟶ UniverseLift.obj.{w} (F.obj d))
  (he : ∀ d, i.app d ≫ families d = b.app d)

include he in
lemma compatible : NerveMovingParameter.vertices K F families ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveMovingParameterRelative.restriction L K i F) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveNaturalBoundary.ofNatTrans L (NerveMovingParameter.lifted F) b) := by
  apply NatTrans.ext
  funext s
  have hzero : dimension s.obj = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ s.property)
  let c := eqToHom (congrArg (NerveMovingParameter.lifted F).obj
    (NerveMovingParameter.start_eq_endpoint_zero s.obj hzero))
  change (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
    (families (NerveSimplexStart.start s.obj) ≫ c)) ≫
      (NerveMovingParameterRelative.restriction L K i F).app s.obj = _
  rw [NerveMovingParameterRelative.restriction_app]
  apply Eq.trans ?_ (NerveNaturalBoundary.ofNatTrans_zero L
    (NerveMovingParameter.lifted F) b s.obj hzero).symm
  have hn : RelativeChoiceSpace.name (families (NerveSimplexStart.start s.obj) ≫ c) ≫
      (pre (i.app (NerveSimplexStart.start s.obj))).app
        (UniverseLift.obj.{w} (F.obj (endpoint s.obj))) =
    RelativeChoiceSpace.name (b.app (NerveSimplexStart.start s.obj) ≫ c) := by
    apply (RelativeChoiceSpace.name_precomp (i.app (NerveSimplexStart.start s.obj))
      (families (NerveSimplexStart.start s.obj) ≫ c)).trans
    exact congrArg RelativeChoiceSpace.name
      ((Category.assoc _ _ _).symm.trans (congrArg (fun e => e ≫ c) (he _)))
  exact (Category.assoc _ _ _).trans
    (congrArg (fun e => SSet.stdSimplex.isTerminalObj₀.from _ ≫ e) hn)


variable (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d)) (hi : ∀ d, Mono (i.app d))

/-- Keep every whole original family and every strict boundary in one all-center system. -/
def extend : NerveMovingParameter.System K F :=
  NerveMovingParameterRelative.extendFamilies L K i F hp hi
    (NerveNaturalBoundary.ofNatTrans L (NerveMovingParameter.lifted F) b) families
    (compatible L K F i b families he)

lemma extend_evaluate (d : D) : NerveMovingParameter.evaluate K F
    (extend L K F i b families he hp hi) d = families d :=
  NerveMovingParameterRelative.extendFamilies_evaluate _ _ _ _ _ _ _ _ _ d

lemma extend_boundary : extend L K F i b families he hp hi ≫
    NerveMovingParameterRelative.restriction L K i F =
      NerveNaturalBoundary.ofNatTrans L (NerveMovingParameter.lifted F) b :=
  NerveMovingParameterRelative.extendFamilies_boundary _ _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveRelativeNaturalBoundary
