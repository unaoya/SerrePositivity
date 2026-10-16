module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterMaps
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveNaturalBoundary

/-! # Transport laws retaining canonical whole moving boundaries -/

@[expose] public section
universe w uD vD uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveBiparameterMaps
variable {D : Type uD} [Category.{vD} D] (V K F G : D ⥤ SSet.{w})
  (i : V ⟶ K) (p : F ⟶ G)

lemma target_restriction : targetMap K F G p ≫ restriction V K G i =
    restriction V K F i ≫ targetMap V F G p := by
  apply NatTrans.ext
  funext s
  simp only [NatTrans.comp_app, restriction_app, targetMap_app]
  exact (pre_comm_ihom_map (i.app (NerveSimplexStart.start s)) (p.app (endpoint s))).symm

variable {E : Type uE} [Category.{vE} E] (H : E ⥤ D)

lemma reindex_restriction (a : NerveBiparameter.System K F) :
    reindex V F H (a ≫ restriction V K F i) = reindex K F H a ≫
      restriction (H ⋙ V) (H ⋙ K) (H ⋙ F) (Functor.whiskerLeft H i) := by
  apply NatTrans.ext
  funext s
  rfl

lemma reindex_natural (b : K ⟶ F) :
    reindex K F H (NerveNaturalBoundary.ofNatTrans K F b) =
      NerveNaturalBoundary.ofNatTrans (H ⋙ K) (H ⋙ F) (Functor.whiskerLeft H b) := by
  apply NatTrans.ext
  funext s
  rfl

lemma restrict_natural (b : K ⟶ F) :
    NerveNaturalBoundary.ofNatTrans K F b ≫ restriction V K F i =
      NerveNaturalBoundary.ofNatTrans V F (i ≫ b) := by
  apply NatTrans.ext
  funext s
  change (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
    (b.app (NerveSimplexStart.start s) ≫ F.map (NerveNaturalBoundary.whole s))) ≫
      (pre (i.app (NerveSimplexStart.start s))).app (F.obj (endpoint s)) = _
  apply (Category.assoc _ _ _).trans
  exact congrArg (fun e => SSet.stdSimplex.isTerminalObj₀.from _ ≫ e)
    ((RelativeChoiceSpace.name_precomp (i.app (NerveSimplexStart.start s))
      (b.app (NerveSimplexStart.start s) ≫ F.map (NerveNaturalBoundary.whole s))).trans
        (congrArg RelativeChoiceSpace.name (Category.assoc _ _ _).symm))

lemma mapTarget_natural (b : K ⟶ F) :
    NerveNaturalBoundary.ofNatTrans K F b ≫ targetMap K F G p =
      NerveNaturalBoundary.ofNatTrans K G (b ≫ p) := by
  apply NatTrans.ext
  funext s
  change (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
    (b.app (NerveSimplexStart.start s) ≫ F.map (NerveNaturalBoundary.whole s))) ≫
      (ihom (K.obj (NerveSimplexStart.start s))).map (p.app (endpoint s)) = _
  rw [Category.assoc, RelativeChoiceSpace.name_postcomp, Category.assoc,
    p.naturality, ← Category.assoc]
  rfl

end SerrePositivity.SimplicialModel.NerveBiparameterMaps
