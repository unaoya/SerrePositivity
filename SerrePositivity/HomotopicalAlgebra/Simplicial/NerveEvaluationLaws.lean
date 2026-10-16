module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveProductParameter

/-! # Actual objectwise evaluation of whole restriction and natural-boundary equations -/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveEvaluationLaws
variable {D : Type uD} [Category.{vD} D] (K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v})

lemma restriction (L : D ⥤ SSet.{max w v}) (i : L ⟶ K)
    (a : NerveMovingParameter.System K F) (b : NerveMovingParameter.System L F)
    (h : a ≫ NerveBiparameterMaps.restriction L K (NerveMovingParameter.lifted F) i = b)
    (d : D) : i.app d ≫ NerveMovingParameter.evaluate K F a d =
      NerveMovingParameter.evaluate L F b d :=
  (NerveBiparameterMaps.evaluate_restrict K F a L i d).symm.trans
    (congrArg (fun z => NerveMovingParameter.evaluate L F z d) h)

lemma natural (b : K ⟶ NerveMovingParameter.lifted.{w} F) (d : D) :
    NerveMovingParameter.evaluate K F
      (NerveNaturalBoundary.ofNatTrans K (NerveMovingParameter.lifted F) b) d = b.app d := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (NerveNaturalBoundary.ofNatTrans K (NerveMovingParameter.lifted F) b).app
      (ofChain (ComposableArrows.mk₀ d))) = _
  rw [NerveNaturalBoundary.ofNatTrans_zero _ _ _ _ rfl]
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name (b.app d ≫ 𝟙 _))) = _
  rw [Category.comp_id, show SSet.stdSimplex.isTerminalObj₀.from
    (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 0)) = 𝟙 _ from
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _, Category.id_comp,
    RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry']

lemma expand (T : SSet.{max w v}) (a : NerveMovingParameter.System K F) (d : D) :
    NerveMovingParameter.evaluate (NerveCylinderBoundary.product K T) F
      (NerveProductParameter.expand K (NerveMovingParameter.lifted F) T a) d =
    (NerveProductParameter.projection K T).app d ≫ NerveMovingParameter.evaluate K F a d :=
  NerveBiparameterMaps.evaluate_restrict K F a _ _ d

end SerrePositivity.SimplicialModel.NerveEvaluationLaws
