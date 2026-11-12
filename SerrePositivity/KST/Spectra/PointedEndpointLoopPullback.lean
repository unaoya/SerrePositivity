module

public import SerrePositivity.KST.Spectra.BasedPathLoopRestriction

/-!
概要：二端点を潰した円からの点つき Hom は path 終点の点つき引き戻しである。
方針：反変内部 Hom に cofiber の pushout を写し、一点と単位 Hom の同型で底を揃える。
規約：Kan 性を仮定しない点つき同型。使われ方：native loop 比較の各段の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
namespace SerrePositivity.KST.Spectra

/-- 一点を源とする内部 Hom は点つき圏の零対象。 -/
lemma pointedHomPoint_isZero (Y : PointedSimplicialSet.{u}) :
    IsZero (PointedObject.basedHom (PointedObject.point : PointedSimplicialSet.{u}) Y) := by
  let T := PointedObject.basedHom (PointedObject.point : PointedSimplicialSet.{u}) Y
  have : IsIso T.hom := isIso_of_isTerminal isTerminalTensorUnit (homPointIsTerminal Y) _
  let e : (PointedObject.point : PointedSimplicialSet.{u}) ≅ T :=
    Under.isoMk (asIso T.hom) (by change (𝟙 _) ≫ T.hom = T.hom; simp)
  exact PointedObject.point_isZero.of_iso e.symm

/-- cofiber からの内部 Hom は点つき圏でも引き戻し。 -/
lemma pointedCofiberMapping_isPullback {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (Y : PointedSimplicialSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection i) Y)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.fromPoint (pointedCofiber i)) Y)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.toPoint A) Y) := by
  have h := ((pointedCofiber_isPushout i).op.flip).map (internalHom.flip.obj Y)
  change IsPullback ((MonoidalClosed.pre (pointedCofiberProjection i)).app Y)
    ((MonoidalClosed.pre (PointedObject.fromPoint (pointedCofiber i))).app Y)
    ((MonoidalClosed.pre i).app Y) ((MonoidalClosed.pre (PointedObject.toPoint A)).app Y) at h
  simpa only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] using h

/-- 円の写像対象は path 終点の基点上の実際の点つき引き戻し。 -/
lemma pointedEndpointLoop_isPullback (Y : PointedSimplicialSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Y)
      (PointedObject.toPoint (PointedObject.basedHom endpointCircle.{u} Y))
      (pathEndpoint Y) (PointedObject.fromPoint Y) := by
  let T := PointedObject.basedHom (PointedObject.point : PointedSimplicialSet.{u}) Y
  let e₃ : T ≅ PointedObject.point := (pointedHomPoint_isZero Y).iso PointedObject.point_isZero
  let e₄ := MonoidalClosed.unitIsoSelf (X := Y)
  have h := pointedCofiberMapping_isPullback _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u} Y
  refine h.of_iso (Iso.refl _) (Iso.refl _) e₃ e₄ ?_ ?_ ?_ ?_
  · simp
  · exact PointedObject.point_isZero.eq_of_tgt _ _
  · exact (Category.id_comp _).symm
  · exact (pointedHomPoint_isZero Y).eq_of_src _ _

/-- path 終点の点つき引き戻しと円の写像対象の厳密な同型。 -/
def pointedEndpointLoopIso (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHom endpointCircle.{u} Y ≅
      pullback (pathEndpoint Y) (PointedObject.fromPoint Y) :=
  (pointedEndpointLoop_isPullback Y).isoPullback

@[reassoc (attr := simp)]
lemma pointedEndpointLoopIso_hom_fst (Y : PointedSimplicialSet.{u}) :
    (pointedEndpointLoopIso Y).hom ≫ pullback.fst (pathEndpoint Y) (PointedObject.fromPoint Y) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Y :=
  (pointedEndpointLoop_isPullback Y).isoPullback_hom_fst

end SerrePositivity.KST.Spectra
