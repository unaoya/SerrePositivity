module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveProductParameter

/-! # Whole-system composition laws for actual parameter and value transports -/

@[expose] public section
universe w uD vD uE vE uJ vJ
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveBiparameterMaps
variable {D : Type uD} [Category.{vD} D] (K F G Q : D ⥤ SSet.{w})
  (p : F ⟶ G) (q : G ⟶ Q)

lemma targetMap_comp : targetMap K F G p ≫ targetMap K G Q q = targetMap K F Q (p ≫ q) := by
  apply NatTrans.ext
  funext s
  simp only [NatTrans.comp_app, targetMap_app]
  exact ((ihom (K.obj (NerveSimplexStart.start s))).map_comp (p.app (endpoint s))
    (q.app (endpoint s))).symm

variable {E : Type uE} [Category.{vE} E] (H : E ⥤ D)

lemma reindex_mapTarget (a : NerveBiparameter.System K F) :
    reindex K G H (mapTarget K F G p a) = mapTarget (H ⋙ K) (H ⋙ F) (H ⋙ G)
      (Functor.whiskerLeft H p) (reindex K F H a) := by
  apply NatTrans.ext
  funext s
  rfl

lemma reindex_reindex {J : Type uJ} [Category.{vJ} J] (L : J ⥤ E)
    (a : NerveBiparameter.System K F) : reindex (H ⋙ K) (H ⋙ F) L (reindex K F H a) =
      reindex K F (L ⋙ H) a := by
  apply NatTrans.ext
  funext s
  rfl

/-- Equal indexing functors transport the very same whole system, not just homotopic choices. -/
lemma reindex_eq_transport {H' : E ⥤ D} (h : H' = H) (a : NerveBiparameter.System K F) :
    mapTarget (H' ⋙ K) (H' ⋙ F) (H ⋙ F) (Functor.whiskerRight (eqToHom h) F)
      (reindex K F H' a) =
    restrict (H' ⋙ K) (H ⋙ K) (H ⋙ F) (Functor.whiskerRight (eqToHom h) K)
      (reindex K F H a) := by
  subst H'
  apply NatTrans.ext
  funext s
  rw [mapTarget_component, restrict_component]
  change a.app ((NerveCoherentReindex.index H).obj s) ≫
    (ihom (K.obj (H.obj (NerveSimplexStart.start s)))).map
      (F.map (𝟙 (H.obj (endpoint s)))) =
    a.app ((NerveCoherentReindex.index H).obj s) ≫
      (pre (K.map (𝟙 (H.obj (NerveSimplexStart.start s))))).app (F.obj (H.obj (endpoint s)))
  have hi : (ihom (K.obj (H.obj (NerveSimplexStart.start s)))).map
      (F.map (𝟙 (H.obj (endpoint s)))) =
      (pre (K.map (𝟙 (H.obj (NerveSimplexStart.start s))))).app (F.obj (H.obj (endpoint s))) := by
    rw [F.map_id, K.map_id, CategoryTheory.Functor.map_id, pre_id]
    rfl
  exact congrArg (fun k => a.app ((NerveCoherentReindex.index H).obj s) ≫ k) hi

lemma reindex_expand (T : SSet.{w}) (a : NerveBiparameter.System K F) :
    reindex (NerveCylinderBoundary.product K T) F H (NerveProductParameter.expand K F T a) =
      NerveProductParameter.expand (H ⋙ K) (H ⋙ F) T (reindex K F H a) := by
  apply NatTrans.ext
  funext s
  rfl

lemma expand_mapTarget (T : SSet.{w}) (a : NerveBiparameter.System K F) :
    NerveProductParameter.expand K G T (mapTarget K F G p a) =
      mapTarget (NerveCylinderBoundary.product K T) F G p
        (NerveProductParameter.expand K F T a) := by
  change (a ≫ targetMap K F G p) ≫ restriction _ _ _ _ =
    (a ≫ restriction _ _ _ _) ≫ targetMap _ _ _ _
  rw [Category.assoc, target_restriction, ← Category.assoc]

end SerrePositivity.SimplicialModel.NerveBiparameterMaps
