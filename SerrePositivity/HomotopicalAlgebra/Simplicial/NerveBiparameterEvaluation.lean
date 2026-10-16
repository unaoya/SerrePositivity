module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws

/-! # Recovering actual whole maps after parameter and value transport -/

@[expose] public section
universe w v uD vD uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveBiparameterMaps
variable {D : Type uD} [Category.{vD} D]
  (K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v}) (a : NerveMovingParameter.System K F)

lemma name_evaluate (d : D) : RelativeChoiceSpace.name (NerveMovingParameter.evaluate K F a d) =
    a.app (ofChain (ComposableArrows.mk₀ d)) := by
  change RelativeChoiceSpace.pointUnitIso.hom ≫
    curry' (uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
      a.app (ofChain (ComposableArrows.mk₀ d)))) = _
  rw [curry'_uncurry', Iso.hom_inv_id_assoc]

lemma evaluate_mapTarget (G : D ⥤ SSet.{v}) (p : F ⟶ G) (d : D) :
    NerveMovingParameter.evaluate K G
      (mapTarget K (NerveMovingParameter.lifted F) (NerveMovingParameter.lifted G)
        (Functor.whiskerRight p SSet.uliftFunctor.{w, v}) a) d =
      NerveMovingParameter.evaluate K F a d ≫ UniverseLift.map.{w} (p.app d) := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (a.app (ofChain (ComposableArrows.mk₀ d)) ≫
      (ihom (K.obj d)).map (UniverseLift.map.{w} (p.app d)))) = _
  rw [← name_evaluate K F a d, RelativeChoiceSpace.name_postcomp,
    RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry']

lemma evaluate_restrict (L : D ⥤ SSet.{max w v}) (i : L ⟶ K) (d : D) :
    NerveMovingParameter.evaluate L F (restrict L K (NerveMovingParameter.lifted F) i a) d =
      i.app d ≫ NerveMovingParameter.evaluate K F a d := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (a.app (ofChain (ComposableArrows.mk₀ d)) ≫
      (pre (i.app d)).app (UniverseLift.obj.{w} (F.obj d)))) = _
  rw [← name_evaluate K F a d]
  exact (congrArg (fun k => uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫ k))
    (RelativeChoiceSpace.name_precomp (i.app d) (NerveMovingParameter.evaluate K F a d))).trans
      (by rw [RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry'])

variable {E : Type uE} [Category.{vE} E] (H : E ⥤ D)

lemma evaluate_reindex (e : E) : NerveMovingParameter.evaluate (H ⋙ K) (H ⋙ F)
    (reindex K (NerveMovingParameter.lifted F) H a) e =
      NerveMovingParameter.evaluate K F a (H.obj e) := by
  dsimp only [NerveMovingParameter.evaluate, reindex]
  congr 3
  apply congrArg Opposite.op
  change (nerve D).elementsMk (Opposite.op (SimplexCategory.mk 0))
    (ComposableArrows.mk₀ e ⋙ H) =
      (nerve D).elementsMk (Opposite.op (SimplexCategory.mk 0)) (ComposableArrows.mk₀ (H.obj e))
  apply congrArg ((nerve D).elementsMk (Opposite.op (SimplexCategory.mk 0)))
  change ComposableArrows.mk₀ e ⋙ H = ComposableArrows.mk₀ (H.obj e)
  exact ComposableArrows.ext₀ rfl

end SerrePositivity.SimplicialModel.NerveBiparameterMaps
